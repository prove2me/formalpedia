-- Prove2me | solution 1 for syracuse_descent_new23_step12_chunk01_seven_mod32
-- status  : ACCEPTED   (prove)
-- author  : @FakeMink
-- created : 2026-10-01T17:18:58.66898+00:00
-- url     : https://prove2.me/submissions/33307d1c-a865-43ed-a9f6-da6be5448711

import Definitions.Def_syracuseSevenMod32New23Step12Chunk01Classes
import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Std
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Insert

set_option autoImplicit false

namespace Session67Parents

/-- A certified power of two and odd quotient determine one accelerated step exactly. -/
theorem syracuseStep_eq_of_factor {n q : ℕ} (e : ℕ)
    (hfactor : 3 * n + 1 = 2 ^ e * q) (hodd : q % 2 = 1) :
    syracuseStep n = q := by
  unfold syracuseStep
  rw [hfactor]
  apply Nat.ordCompl_pow_mul_of_not_dvd e Nat.prime_two
  intro hdvd
  have hzero : q % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
  omega

/-- If the quotient might still be even, removing further factors can only reduce it. -/
theorem syracuseStep_le_of_factor {n q : ℕ} (e : ℕ)
    (hfactor : 3 * n + 1 = 2 ^ e * q) :
    syracuseStep n ≤ q := by
  unfold syracuseStep
  rw [hfactor, Nat.ordCompl_self_pow_mul q e Nat.prime_two]
  exact Nat.ordCompl_le q 2


end Session67Parents

namespace Session67Parents
namespace AffineTrace

/-- A proposed division by `2 ^ e`, with explicit output affine coefficients. -/
structure Step where
  e : ℕ
  nextSlope : ℕ
  nextIntercept : ℕ
  deriving DecidableEq, Repr

/-- Each edge has two factor identities. Nonfinal outputs must be odd for every
parameter; the final output is only an upper bound and needs no parity condition.
An empty trace identifies the starting and ending coefficients. -/
def Valid (a b endA endB : ℕ) : List Step → Prop
  | [] => a = endA ∧ b = endB
  | s :: rest =>
      3 * a = 2 ^ s.e * s.nextSlope ∧
      3 * b + 1 = 2 ^ s.e * s.nextIntercept ∧
      (rest = [] ∨ (s.nextSlope % 2 = 0 ∧ s.nextIntercept % 2 = 1)) ∧
      Valid s.nextSlope s.nextIntercept endA endB rest

/-- Recursive, kernel-computable certificate checking; closed certificates use `decide`. -/
instance instDecidableValid (a b endA endB : ℕ) (trace : List Step) :
    Decidable (Valid a b endA endB trace) :=
  match trace with
  | [] => inferInstanceAs (Decidable (a = endA ∧ b = endB))
  | s :: rest =>
      letI := instDecidableValid s.nextSlope s.nextIntercept endA endB rest
      inferInstanceAs (Decidable
        (3 * a = 2 ^ s.e * s.nextSlope ∧
         3 * b + 1 = 2 ^ s.e * s.nextIntercept ∧
         (rest = [] ∨ (s.nextSlope % 2 = 0 ∧ s.nextIntercept % 2 = 1)) ∧
         Valid s.nextSlope s.nextIntercept endA endB rest))

/-- Coefficient identities give the factor identity for every parameter. -/
theorem factor_of_coefficients {a b : ℕ} {s : Step}
    (ha : 3 * a = 2 ^ s.e * s.nextSlope)
    (hb : 3 * b + 1 = 2 ^ s.e * s.nextIntercept) (k : ℕ) :
    3 * (a * k + b) + 1 = 2 ^ s.e * (s.nextSlope * k + s.nextIntercept) := by
  calc
    3 * (a * k + b) + 1 = (3 * a) * k + (3 * b + 1) := by ring
    _ = (2 ^ s.e * s.nextSlope) * k + (2 ^ s.e * s.nextIntercept) := by rw [ha, hb]
    _ = 2 ^ s.e * (s.nextSlope * k + s.nextIntercept) := by ring

/-- Soundness uses exact nonfinal edges and one final inequality, never monotonicity
of the Syracuse map. -/
theorem sound {a b endA endB : ℕ} {trace : List Step}
    (h : Valid a b endA endB trace) :
    ∀ k : ℕ, syracuseStep^[trace.length] (a * k + b) ≤ endA * k + endB := by
  induction trace generalizing a b with
  | nil =>
      rcases h with ⟨rfl, rfl⟩
      intro k
      exact le_rfl
  | cons s rest ih =>
      rcases h with ⟨ha, hb, hparity, hrest⟩
      intro k
      have hfactor := factor_of_coefficients ha hb k
      cases rest with
      | nil =>
          rcases hrest with ⟨rfl, rfl⟩
          simpa using syracuseStep_le_of_factor s.e hfactor
      | cons t rest =>
          have hp : s.nextSlope % 2 = 0 ∧ s.nextIntercept % 2 = 1 :=
            hparity.resolve_left (by simp)
          have hodd : (s.nextSlope * k + s.nextIntercept) % 2 = 1 := by
            simp [Nat.add_mod, Nat.mul_mod, hp.1, hp.2]
          rw [List.length_cons, Function.iterate_succ_apply,
            syracuseStep_eq_of_factor s.e hfactor hodd]
          exact ih hrest k

/-- Slope nonincrease and strict intercept decrease imply strict affine descent. -/
theorem affine_lt_of_coefficients {a b endA endB : ℕ}
    (ha : endA ≤ a) (hb : endB < b) (k : ℕ) :
    endA * k + endB < a * k + b := by
  have hmul := Nat.mul_le_mul_right k ha
  omega

/-- A valid trace with descending endpoint coefficients proves strict descent. -/
theorem strict_descent {a b endA endB : ℕ} {trace : List Step}
    (h : Valid a b endA endB trace) (ha : endA ≤ a) (hb : endB < b) :
    ∀ k : ℕ, syracuseStep^[trace.length] (a * k + b) < a * k + b := by
  intro k
  exact lt_of_le_of_lt (sound h k) (affine_lt_of_coefficients ha hb k)


end AffineTrace
end Session67Parents

namespace Session67Parents
namespace Batch

open AffineTrace

/-- A residue and explicit finite affine trace, not an asserted theorem. -/
structure Certificate where
  residue : ℕ
  endA : ℕ
  endB : ℕ
  trace : List Step
  deriving DecidableEq, Repr

/-- Each accepted certificate proves 12-step descent on its entire progression. -/
def Accepted (c : Certificate) : Prop :=
  Valid 8388608 c.residue c.endA c.endB c.trace ∧
  c.trace.length = 12 ∧ c.endA ≤ 8388608 ∧ c.endB < c.residue

instance (c : Certificate) : Decidable (Accepted c) := by
  unfold Accepted
  infer_instance

def residues (cs : List Certificate) : List ℕ := cs.map Certificate.residue

theorem descent_of_accepted {c : Certificate} (h : Accepted c) (k : ℕ) :
    syracuseStep^[12] (8388608 * k + c.residue) < 8388608 * k + c.residue := by
  rcases h with ⟨hvalid, hlength, ha, hb⟩
  simpa only [hlength] using AffineTrace.strict_descent hvalid ha hb k

theorem descent_of_residue {c : Certificate} (h : Accepted c)
    (n : ℕ) (hn : n % 8388608 = c.residue) : syracuseStep^[12] n < n := by
  have hform : n = 8388608 * (n / 8388608) + c.residue := by omega
  rw [hform]
  exact descent_of_accepted h (n / 8388608)

/-- The proof consumes finite, kernel-checked certificate acceptance, not search output. -/
theorem descent_of_mem (cs : List Certificate) (hchecked : ∀ c ∈ cs, Accepted c)
    (n : ℕ) (h : n % 8388608 ∈ residues cs) : syracuseStep^[12] n < n := by
  obtain ⟨c, hc, hr⟩ := List.mem_map.mp h
  exact descent_of_residue (hchecked c hc) n hr.symm


end Batch
end Session67Parents

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Session67Parents
open AffineTrace Batch

/-- Build proposed affine edges from exponents; acceptance checks every identity. -/
def traceFrom (a b : ℕ) : List ℕ → ℕ × ℕ × List AffineTrace.Step
  | [] => (a, b, [])
  | e :: es =>
      let nextA := 3 * a / 2 ^ e
      let nextB := (3 * b + 1) / 2 ^ e
      let tail := traceFrom nextA nextB es
      (tail.1, tail.2.1, ⟨e, nextA, nextB⟩ :: tail.2.2)

def certificateFrom (r : ℕ) (es : List ℕ) : Batch.Certificate :=
  let result := traceFrom 8388608 r es
  ⟨r, result.1, result.2.1, result.2.2⟩

def certificates : List Certificate :=
[  certificateFrom 1127 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7],
  certificateFrom 10471 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6],
  certificateFrom 18663 [1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6],
  certificateFrom 38631 [1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5],
  certificateFrom 51559 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7],
  certificateFrom 82023 [1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6],
  certificateFrom 86695 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 5],
  certificateFrom 94887 [1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 5],
  certificateFrom 124263 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6],
  certificateFrom 128935 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 7],
  certificateFrom 132455 [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6],
  certificateFrom 137127 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 5],
  certificateFrom 152391 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8],
  certificateFrom 152423 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7],
  certificateFrom 160583 [1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6],
  certificateFrom 214503 [1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5],
  certificateFrom 216935 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10],
  certificateFrom 219239 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5],
  certificateFrom 227431 [1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5],
  certificateFrom 240359 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5],
  certificateFrom 252071 [1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 6],
  certificateFrom 270823 [1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6],
  certificateFrom 275559 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8],
  certificateFrom 283751 [1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6],
  certificateFrom 313063 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6],
  certificateFrom 321255 [1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6],
  certificateFrom 356423 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 5],
  certificateFrom 378695 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6],
  certificateFrom 381095 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 7],
  certificateFrom 386887 [1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6],
  certificateFrom 389287 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 5],
  certificateFrom 406855 [1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5],
  certificateFrom 412775 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9],
  certificateFrom 420967 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5],
  certificateFrom 498343 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 5],
  certificateFrom 514791 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6],
  certificateFrom 530023 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7],
  certificateFrom 567527 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7],
  certificateFrom 582727 [1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 5],
  certificateFrom 608583 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5],
  certificateFrom 639047 [1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 6],
  certificateFrom 668391 [1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5],
  certificateFrom 681287 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6],
  certificateFrom 681319 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7],
  certificateFrom 689479 [1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6],
  certificateFrom 690663 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6],
  certificateFrom 698855 [1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6],
  certificateFrom 724647 [1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 5],
  certificateFrom 762215 [1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6],
  certificateFrom 780967 [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 6],
  certificateFrom 804455 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8],
  certificateFrom 812647 [1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6],
  certificateFrom 854887 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6],
  certificateFrom 870119 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7],
  certificateFrom 883015 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6],
  certificateFrom 899431 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5],
  certificateFrom 907623 [1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5],
  certificateFrom 935751 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7],
  certificateFrom 955751 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8],
  certificateFrom 963943 [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6],
  certificateFrom 1027239 [1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 5],
  certificateFrom 1030759 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6],
  certificateFrom 1036615 [1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5],
  certificateFrom 1038951 [1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6],
  certificateFrom 1056615 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8],
  certificateFrom 1058887 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 6],
  certificateFrom 1058919 [1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5],
  certificateFrom 1067079 [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 6],
  certificateFrom 1071847 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7],
  certificateFrom 1083559 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 6],
  certificateFrom 1092967 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9],
  certificateFrom 1101159 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5],
  certificateFrom 1102311 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6],
  certificateFrom 1144551 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8],
  certificateFrom 1152743 [1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6],
  certificateFrom 1197287 [1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5],
  certificateFrom 1200807 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 6],
  certificateFrom 1208999 [1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 6],
  certificateFrom 1210215 [1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5],
  certificateFrom 1238343 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7],
  certificateFrom 1247719 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7],
  certificateFrom 1251239 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 6],
  certificateFrom 1260647 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5],
  certificateFrom 1328615 [1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6],
  certificateFrom 1333351 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6],
  certificateFrom 1341543 [1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6],
  certificateFrom 1354471 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6],
  certificateFrom 1404839 [1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 5],
  certificateFrom 1411943 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7],
  certificateFrom 1440071 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7],
  certificateFrom 1447079 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 5],
  certificateFrom 1455271 [1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 5],
  certificateFrom 1470535 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 6],
  certificateFrom 1476455 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8],
  certificateFrom 1499879 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5],
  certificateFrom 1503399 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 6],
  certificateFrom 1512775 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8],
  certificateFrom 1520967 [1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6],
  certificateFrom 1535079 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6],
  certificateFrom 1565511 [1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5],
  certificateFrom 1587815 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7],
  certificateFrom 1612455 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 6],
  certificateFrom 1615943 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 7],
  certificateFrom 1617127 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5],
  certificateFrom 1625319 [1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5],
  certificateFrom 1640615 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 7],
  certificateFrom 1648807 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 5],
  certificateFrom 1659367 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7],
  certificateFrom 1667559 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5],
  certificateFrom 1688679 [1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5],
  certificateFrom 1696839 [1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 6],
  certificateFrom 1722695 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6],
  certificateFrom 1739111 [1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5],
  certificateFrom 1757863 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 7],
  certificateFrom 1782503 [1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6],
  certificateFrom 1808295 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 7],
  certificateFrom 1838759 [1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 6],
  certificateFrom 1839975 [1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5],
  certificateFrom 1858727 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 5],
  certificateFrom 1868103 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5],
  certificateFrom 1890407 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7],
  certificateFrom 1911527 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7],
  certificateFrom 1919719 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5],
  certificateFrom 1940839 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5],
  certificateFrom 1985351 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5],
  certificateFrom 1993543 [1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5],
  certificateFrom 2013543 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6],
  certificateFrom 2021735 [1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6],
  certificateFrom 2027591 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 7],
  certificateFrom 2028775 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5],
  certificateFrom 2035783 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 5],
  certificateFrom 2060455 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 7],
  certificateFrom 2092135 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7],
  certificateFrom 2106215 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8],
  certificateFrom 2141351 [1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 6],
  certificateFrom 2150727 [1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6],
  certificateFrom 2164839 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8],
  certificateFrom 2169511 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 7],
  certificateFrom 2173031 [1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6],
  certificateFrom 2177703 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 5],
  certificateFrom 2215271 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6],
  certificateFrom 2217575 [1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5],
  certificateFrom 2255079 [1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5],
  certificateFrom 2259815 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5],
  certificateFrom 2268007 [1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5],
  certificateFrom 2279751 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7],
  certificateFrom 2287943 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5],
  certificateFrom 2311399 [1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6],
  certificateFrom 2316135 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8],
  certificateFrom 2324327 [1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6],
  certificateFrom 2368871 [1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5],
  certificateFrom 2374759 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6],
  certificateFrom 2396999 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5],
  certificateFrom 2518951 [1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 6],
  certificateFrom 2520167 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5],
  certificateFrom 2557671 [1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5],
  certificateFrom 2561191 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 6],
  certificateFrom 2569383 [1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 6],
  certificateFrom 2570599 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7],
  certificateFrom 2613991 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6],
  certificateFrom 2623303 [1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5],
  certificateFrom 2637415 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5],
  certificateFrom 2645607 [1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5],
  certificateFrom 2656167 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 5],
  certificateFrom 2664359 [1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 5],
  certificateFrom 2679623 [1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6],
  certificateFrom 2731239 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6],
  certificateFrom 2739431 [1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6],
  certificateFrom 2762919 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 6],
  certificateFrom 2772327 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7],
  certificateFrom 2781671 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6],
  certificateFrom 2802791 [1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6],
  certificateFrom 2845031 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8],
  certificateFrom 2853223 [1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6],
  certificateFrom 2925895 [1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5],
  certificateFrom 2931815 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7],
  certificateFrom 2935271 [1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5],
  certificateFrom 2940007 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5],
  certificateFrom 2945895 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8],
  certificateFrom 2954087 [1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6],
  certificateFrom 2972839 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 6],
  certificateFrom 2977511 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5],
  certificateFrom 2982215 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6],
  certificateFrom 2985703 [1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5],
  certificateFrom 3033831 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6],
  certificateFrom 3049063 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5],
  certificateFrom 3054951 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6],
  certificateFrom 3099463 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6],
  certificateFrom 3099495 [1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5],
  certificateFrom 3107655 [1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6],
  certificateFrom 3118247 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 7],
  certificateFrom 3142887 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6],
  certificateFrom 3149895 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 6],
  certificateFrom 3171047 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7],
  certificateFrom 3179239 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5],
  certificateFrom 3200359 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5],
  certificateFrom 3275367 [1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5],
  certificateFrom 3288295 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7],
  certificateFrom 3291815 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 6],
  certificateFrom 3293031 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9],
  certificateFrom 3301223 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5],
  certificateFrom 3303495 [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 5],
  certificateFrom 3319975 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 7],
  certificateFrom 3331687 [1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6],
  certificateFrom 3338727 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7],
  certificateFrom 3345735 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5],
  certificateFrom 3353927 [1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5],
  certificateFrom 3369191 [1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6],
  certificateFrom 3373927 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6],
  certificateFrom 3382119 [1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6],
  certificateFrom 3389159 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5],
  certificateFrom 3402055 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6],
  certificateFrom 3445415 [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 5],
  certificateFrom 3482983 [1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6],
  certificateFrom 3495847 [1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 5],
  certificateFrom 3511111 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6],
  certificateFrom 3529895 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 7],
  certificateFrom 3538087 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 5],
  certificateFrom 3539271 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7],
  certificateFrom 3547463 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5],
  certificateFrom 3577959 [1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5],
  certificateFrom 3590887 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7],
  certificateFrom 3612007 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7],
  certificateFrom 3620199 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5],
  certificateFrom 3634279 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6],
  certificateFrom 3656519 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7],
  certificateFrom 3671783 [1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6],
  certificateFrom 3699943 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7],
  certificateFrom 3706951 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 7],
  certificateFrom 3708135 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5],
  certificateFrom 3712871 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9],
  certificateFrom 3713959 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 5],
  certificateFrom 3721063 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5],
  certificateFrom 3722151 [1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 5],
  certificateFrom 3737415 [1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6],
  certificateFrom 3748007 [1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 5],
  certificateFrom 3751527 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6],
  certificateFrom 3757383 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5],
  certificateFrom 3759719 [1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6],
  certificateFrom 3770279 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 6],
  certificateFrom 3778471 [1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 6],
  certificateFrom 3848871 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 7],
  certificateFrom 3930983 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7],
  certificateFrom 3959111 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7],
  certificateFrom 3997799 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5],
  certificateFrom 4005991 [1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5],
  certificateFrom 4014247 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 8],
  certificateFrom 4040007 [1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6],
  certificateFrom 4049383 [1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6],
  certificateFrom 4054119 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6],
  certificateFrom 4068167 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7],
  certificateFrom 4076359 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5],
  certificateFrom 4091623 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6],
  certificateFrom 4099815 [1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6],
  certificateFrom 4163175 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6],
  certificateFrom 4167847 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 5],
  certificateFrom 4176039 [1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 5],
  certificateFrom 4186599 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5],
  certificateFrom 4191335 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7],
  certificateFrom 4194791 [1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5],
  certificateFrom 4199527 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5],
  certificateFrom 4205415 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8],
  certificateFrom 4213607 [1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6],
  certificateFrom 4258151 [1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5],
  certificateFrom 4293351 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6],
  certificateFrom 4308583 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7],
  certificateFrom 4314471 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6],
  certificateFrom 4327335 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 7],
  certificateFrom 4342631 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9],
  certificateFrom 4350823 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5],
  certificateFrom 4389479 [1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6],
  certificateFrom 4409447 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5],
  certificateFrom 4415335 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6],
  certificateFrom 4417607 [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 6],
  certificateFrom 4459847 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6],
  certificateFrom 4468039 [1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6],
  certificateFrom 4503271 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6],
  certificateFrom 4554823 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 5],
  certificateFrom 4559527 [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 6],
  certificateFrom 4560743 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5],
  certificateFrom 4563015 [1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 5],
  certificateFrom 4601767 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 8],
  certificateFrom 4609959 [1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 6],
  certificateFrom 4611175 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7],
  certificateFrom 4648679 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7],
  certificateFrom 4652199 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 6],
  certificateFrom 4661575 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6],
  certificateFrom 4677991 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5],
  certificateFrom 4686183 [1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5],
  certificateFrom 4692071 [1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6],
  certificateFrom 4696743 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 5],
  certificateFrom 4704935 [1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 5],
  certificateFrom 4720231 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7],
  certificateFrom 4728423 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5],
  certificateFrom 4734311 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6],
  certificateFrom 4805799 [1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 5],
  certificateFrom 4822247 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6],
  certificateFrom 4828071 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 6],
  certificateFrom 4835175 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6],
  certificateFrom 4836263 [1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 6],
  certificateFrom 4850407 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7],
  certificateFrom 4853927 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 8],
  certificateFrom 4862119 [1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 6],
  certificateFrom 4871495 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6],
  certificateFrom 4871527 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7],
  certificateFrom 4879719 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5],
  certificateFrom 4972391 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7],
  certificateFrom 4975847 [1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5],
  certificateFrom 5007527 [1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 5],
  certificateFrom 5016903 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7],
  certificateFrom 5026279 [1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5],
  certificateFrom 5060327 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7],
  certificateFrom 5068519 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5],
  certificateFrom 5089639 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5],
  certificateFrom 5111911 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6],
  certificateFrom 5120103 [1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6],
  certificateFrom 5190471 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6],
  certificateFrom 5190503 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5],
  certificateFrom 5209255 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 7],
  certificateFrom 5218631 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7],
  certificateFrom 5244391 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5],
  certificateFrom 5252583 [1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5],
  certificateFrom 5278439 [1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5],
  certificateFrom 5281959 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 6],
  certificateFrom 5290151 [1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 6],
  certificateFrom 5291367 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7],
  certificateFrom 5300711 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6],
  certificateFrom 5308903 [1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6],
  certificateFrom 5313639 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6],
  certificateFrom 5344071 [1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5],
  certificateFrom 5372263 [1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6],
  certificateFrom 5379303 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7],
  certificateFrom 5385127 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 7],
  certificateFrom 5392231 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7],
  certificateFrom 5394503 [1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 5],
  certificateFrom 5428551 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7],
  certificateFrom 5436743 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5],
  certificateFrom 5464935 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6],
  certificateFrom 5523559 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6],
  certificateFrom 5536423 [1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 5],
  certificateFrom 5544679 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8],
  certificateFrom 5612615 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 5],
  certificateFrom 5618535 [1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5],
  certificateFrom 5620807 [1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 5],
  certificateFrom 5646663 [1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5],
  certificateFrom 5668935 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 6],
  certificateFrom 5668967 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7],
  certificateFrom 5674855 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6],
  certificateFrom 5677127 [1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 6],
  certificateFrom 5698279 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5],
  certificateFrom 5706471 [1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5],
  certificateFrom 5747527 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7],
  certificateFrom 5754535 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 5],
  certificateFrom 5762727 [1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 5],
  certificateFrom 5792103 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6],
  certificateFrom 5800295 [1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6],
  certificateFrom 5810855 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 6],
  certificateFrom 5819047 [1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 6],
  certificateFrom 5839015 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 7],
  certificateFrom 5842535 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6],
  certificateFrom 5857767 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7],
  certificateFrom 5870695 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7],
  certificateFrom 5912903 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8],
  certificateFrom 5919911 [1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 6],
  certificateFrom 5993831 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6],
  certificateFrom 5996135 [1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5],
  certificateFrom 6014887 [1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 5],
  certificateFrom 6021991 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7],
  certificateFrom 6057127 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 5],
  certificateFrom 6065319 [1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 5],
  certificateFrom 6066503 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5],
  certificateFrom 6074695 [1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5],
  certificateFrom 6080615 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7],
  certificateFrom 6088807 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5],
  certificateFrom 6089959 [1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6],
  certificateFrom 6113447 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 8],
  certificateFrom 6121639 [1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 6],
  certificateFrom 6132199 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8],
  certificateFrom 6140391 [1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6],
  certificateFrom 6182631 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6],
  certificateFrom 6203751 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6],
  certificateFrom 6225991 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 7],
  certificateFrom 6227175 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5],
  certificateFrom 6231911 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7],
  certificateFrom 6235367 [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5],
  certificateFrom 6240103 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5],
  certificateFrom 6250663 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 9],
  certificateFrom 6258855 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 5],
  certificateFrom 6298727 [1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5],
  certificateFrom 6304615 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6],
  certificateFrom 6336231 [1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5],
  certificateFrom 6349159 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7],
  certificateFrom 6358503 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6],
  certificateFrom 6366695 [1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6],
  certificateFrom 6367911 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 7],
  certificateFrom 6384359 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8],
  certificateFrom 6392551 [1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6],
  certificateFrom 6399591 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7],
  certificateFrom 6434727 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 5],
  certificateFrom 6442919 [1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 5],
  certificateFrom 6450023 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5],
  certificateFrom 6458183 [1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6],
  certificateFrom 6500423 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 8],
  certificateFrom 6508615 [1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 6],
  certificateFrom 6537959 [1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5],
  certificateFrom 6550855 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6],
  certificateFrom 6550887 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7],
  certificateFrom 6564967 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8],
  certificateFrom 6595399 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5],
  certificateFrom 6603591 [1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5],
  certificateFrom 6642343 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 8],
  certificateFrom 6650535 [1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 6],
  certificateFrom 6704455 [1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5],
  certificateFrom 6718567 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5],
  certificateFrom 6726727 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 6],
  certificateFrom 6726759 [1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5],
  certificateFrom 6732647 [1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6],
  certificateFrom 6734919 [1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 6],
  certificateFrom 6739687 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7],
  certificateFrom 6752583 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8],
  certificateFrom 6760775 [1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6],
  certificateFrom 6760807 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7],
  certificateFrom 6768999 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5],
  certificateFrom 6812391 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6],
  certificateFrom 6820583 [1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6],
  certificateFrom 6846375 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 5],
  certificateFrom 6861671 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7],
  certificateFrom 6868647 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 6],
  certificateFrom 6869863 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5],
  certificateFrom 6876839 [1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 6],
  certificateFrom 6896807 [1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 5],
  certificateFrom 6906183 [1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5],
  certificateFrom 6915559 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7],
  certificateFrom 6978919 [1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5],
  certificateFrom 7066855 [1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5],
  certificateFrom 7072679 [1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 5],
  certificateFrom 7098535 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 5],
  certificateFrom 7107911 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7],
  certificateFrom 7110247 [1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6],
  certificateFrom 7128999 [1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 6],
  certificateFrom 7171239 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 6],
  certificateFrom 7179431 [1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 6],
  certificateFrom 7180615 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6],
  certificateFrom 7188807 [1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6],
  certificateFrom 7202919 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6],
  certificateFrom 7245159 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8],
  certificateFrom 7247463 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5],
  certificateFrom 7255655 [1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5],
  certificateFrom 7283783 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 7],
  certificateFrom 7284967 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5],
  certificateFrom 7293159 [1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5],
  certificateFrom 7341287 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6],
  certificateFrom 7349479 [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6],
  certificateFrom 7354215 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6],
  certificateFrom 7356519 [1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5],
  certificateFrom 7369447 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7],
  certificateFrom 7372967 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 6],
  certificateFrom 7398759 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5],
  certificateFrom 7404647 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8],
  certificateFrom 7406951 [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5],
  certificateFrom 7412839 [1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6],
  certificateFrom 7425703 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 7],
  certificateFrom 7435079 [1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5],
  certificateFrom 7450343 [1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6],
  certificateFrom 7526567 [1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 5],
  certificateFrom 7545319 [1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5],
  certificateFrom 7548839 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 6],
  certificateFrom 7557031 [1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 6],
  certificateFrom 7558247 [1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5],
  certificateFrom 7564135 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6],
  certificateFrom 7587559 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5],
  certificateFrom 7595751 [1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5],
  certificateFrom 7643879 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8],
  certificateFrom 7652071 [1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6],
  certificateFrom 7653191 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5],
  certificateFrom 7661383 [1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5],
  certificateFrom 7709511 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6],
  certificateFrom 7717703 [1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6],
  certificateFrom 7728295 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 7],
  certificateFrom 7737671 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7],
  certificateFrom 7759975 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7],
  certificateFrom 7781095 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9],
  certificateFrom 7789287 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5],
  certificateFrom 7818567 [1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6],
  certificateFrom 7832679 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6],
  certificateFrom 7840871 [1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6],
  certificateFrom 7883111 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6],
  certificateFrom 7898343 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7],
  certificateFrom 7911271 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7],
  certificateFrom 7913543 [1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 5],
  certificateFrom 7930023 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 7],
  certificateFrom 7955783 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5],
  certificateFrom 7960487 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 6],
  certificateFrom 7963975 [1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5],
  certificateFrom 7965159 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5],
  certificateFrom 7973351 [1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5],
  certificateFrom 7983975 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6],
  certificateFrom 8002727 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 8],
  certificateFrom 8010919 [1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 6],
  certificateFrom 8012103 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8],
  certificateFrom 8020295 [1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6],
  certificateFrom 8036711 [1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5],
  certificateFrom 8055463 [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 5],
  certificateFrom 8084839 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8],
  certificateFrom 8087143 [1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5],
  certificateFrom 8093031 [1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6],
  certificateFrom 8105895 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 7],
  certificateFrom 8121191 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7],
  certificateFrom 8129383 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5],
  certificateFrom 8149319 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9],
  certificateFrom 8157511 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5],
  certificateFrom 8172775 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8],
  certificateFrom 8180967 [1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6],
  certificateFrom 8186791 [1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 6],
  certificateFrom 8212647 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 6],
  certificateFrom 8238439 [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5],
  certificateFrom 8266567 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7],
  certificateFrom 8305255 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5],
  certificateFrom 8313447 [1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5],
  certificateFrom 8333383 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 5],
  certificateFrom 8341575 [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 5],
  certificateFrom 8358055 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 5],
  certificateFrom 8361575 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6],
  certificateFrom 8369767 [1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6],
  certificateFrom 8376807 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5]]

theorem certificates_checked : ∀ c ∈ certificates, Accepted c := by
  decide +kernel

theorem coverage : (certificates.map Certificate.residue).toFinset =
    syracuseSevenMod32New23Step12Chunk01Classes := by
  decide +kernel

end Session67Parents

theorem solution (n : ℕ)
    (h : n % 8388608 ∈ syracuseSevenMod32New23Step12Chunk01Classes) :
    syracuseStep^[12] n < n := by
  rw [← Session67Parents.coverage] at h
  exact Session67Parents.Batch.descent_of_mem Session67Parents.certificates
    Session67Parents.certificates_checked n (List.mem_toFinset.mp h)

#print axioms Session67Parents.certificates_checked
#print axioms solution
