-- Prove2me | solution 1 for syracuse_descent_new22_step12_seven_mod32
-- status  : ACCEPTED   (prove)
-- author  : @FakeMink
-- created : 2026-10-01T17:18:57.505444+00:00
-- url     : https://prove2.me/submissions/0b00dabc-4ad4-4241-8009-2085a8bdd1c5

import Definitions.Def_syracuseSevenMod32New22Step12Classes
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
  Valid 4194304 c.residue c.endA c.endB c.trace ∧
  c.trace.length = 12 ∧ c.endA ≤ 4194304 ∧ c.endB < c.residue

instance (c : Certificate) : Decidable (Accepted c) := by
  unfold Accepted
  infer_instance

def residues (cs : List Certificate) : List ℕ := cs.map Certificate.residue

theorem descent_of_accepted {c : Certificate} (h : Accepted c) (k : ℕ) :
    syracuseStep^[12] (4194304 * k + c.residue) < 4194304 * k + c.residue := by
  rcases h with ⟨hvalid, hlength, ha, hb⟩
  simpa only [hlength] using AffineTrace.strict_descent hvalid ha hb k

theorem descent_of_residue {c : Certificate} (h : Accepted c)
    (n : ℕ) (hn : n % 4194304 = c.residue) : syracuseStep^[12] n < n := by
  have hform : n = 4194304 * (n / 4194304) + c.residue := by omega
  rw [hform]
  exact descent_of_accepted h (n / 4194304)

/-- The proof consumes finite, kernel-checked certificate acceptance, not search output. -/
theorem descent_of_mem (cs : List Certificate) (hchecked : ∀ c ∈ cs, Accepted c)
    (n : ℕ) (h : n % 4194304 ∈ residues cs) : syracuseStep^[12] n < n := by
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
  let result := traceFrom 4194304 r es
  ⟨r, result.1, result.2.1, result.2.2⟩

def certificates : List Certificate :=
[  certificateFrom 7271 [1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4],
  certificateFrom 9063 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7],
  certificateFrom 13159 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5],
  certificateFrom 44199 [1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 5],
  certificateFrom 44775 [1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4],
  certificateFrom 53575 [1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5],
  certificateFrom 57703 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6],
  certificateFrom 67047 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5],
  certificateFrom 67687 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7],
  certificateFrom 72359 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 6],
  certificateFrom 75239 [1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5],
  certificateFrom 75879 [1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5],
  certificateFrom 76455 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 6],
  certificateFrom 80551 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 4],
  certificateFrom 92903 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7],
  certificateFrom 101095 [1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5],
  certificateFrom 108135 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6],
  certificateFrom 118119 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5],
  certificateFrom 120423 [1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4],
  certificateFrom 143271 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 4],
  certificateFrom 151463 [1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 4],
  certificateFrom 157927 [1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4],
  certificateFrom 158567 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4],
  certificateFrom 162663 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4],
  certificateFrom 166727 [1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5],
  certificateFrom 170855 [1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4],
  certificateFrom 182599 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6],
  certificateFrom 190791 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4],
  certificateFrom 208967 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 7],
  certificateFrom 214247 [1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5],
  certificateFrom 217159 [1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 5],
  certificateFrom 218983 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7],
  certificateFrom 227175 [1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5],
  certificateFrom 246503 [1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4],
  certificateFrom 259399 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5],
  certificateFrom 259431 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6],
  certificateFrom 271719 [1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4],
  certificateFrom 273511 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7],
  certificateFrom 277607 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5],
  certificateFrom 299847 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4],
  certificateFrom 303943 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4],
  certificateFrom 312135 [1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4],
  certificateFrom 350887 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 7],
  certificateFrom 359079 [1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 5],
  certificateFrom 412999 [1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4],
  certificateFrom 421799 [1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 5],
  certificateFrom 423015 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4],
  certificateFrom 427111 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4],
  certificateFrom 435271 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 5],
  certificateFrom 435303 [1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4],
  certificateFrom 441191 [1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5],
  certificateFrom 443463 [1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 5],
  certificateFrom 448231 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6],
  certificateFrom 460519 [1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4],
  certificateFrom 461127 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7],
  certificateFrom 464039 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 5],
  certificateFrom 469319 [1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5],
  certificateFrom 469351 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6],
  certificateFrom 472231 [1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 5],
  certificateFrom 473447 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6],
  certificateFrom 477543 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4],
  certificateFrom 516839 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5],
  certificateFrom 520935 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5],
  certificateFrom 526151 [1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4],
  certificateFrom 529127 [1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5],
  certificateFrom 540263 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4],
  certificateFrom 548455 [1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4],
  certificateFrom 554919 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4],
  certificateFrom 559015 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 4],
  certificateFrom 567207 [1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 4],
  certificateFrom 570215 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6],
  certificateFrom 577191 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 5],
  certificateFrom 578407 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4],
  certificateFrom 582471 [1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5],
  certificateFrom 585383 [1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 5],
  certificateFrom 605351 [1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 4],
  certificateFrom 614727 [1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4],
  certificateFrom 624103 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6],
  certificateFrom 634087 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5],
  certificateFrom 642279 [1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5],
  certificateFrom 665767 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 5],
  certificateFrom 675175 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6],
  certificateFrom 684519 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5],
  certificateFrom 687463 [1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4],
  certificateFrom 705639 [1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5],
  certificateFrom 747879 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7],
  certificateFrom 756071 [1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5],
  certificateFrom 775399 [1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4],
  certificateFrom 781223 [1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 4],
  certificateFrom 807079 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 4],
  certificateFrom 816455 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6],
  certificateFrom 818791 [1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5],
  certificateFrom 828743 [1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4],
  certificateFrom 834663 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6],
  certificateFrom 837543 [1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 5],
  certificateFrom 838119 [1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4],
  certificateFrom 842855 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4],
  certificateFrom 848743 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7],
  certificateFrom 856935 [1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5],
  certificateFrom 875687 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 5],
  certificateFrom 879783 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 5],
  certificateFrom 880359 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4],
  certificateFrom 885063 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5],
  certificateFrom 887975 [1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 5],
  certificateFrom 888551 [1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4],
  certificateFrom 889159 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5],
  certificateFrom 897351 [1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5],
  certificateFrom 911463 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5],
  certificateFrom 936679 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5],
  certificateFrom 951911 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4],
  certificateFrom 953703 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7],
  certificateFrom 956007 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4],
  certificateFrom 957799 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5],
  certificateFrom 964199 [1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4],
  certificateFrom 992327 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 6],
  certificateFrom 993511 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4],
  certificateFrom 1001703 [1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4],
  certificateFrom 1002311 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5],
  certificateFrom 1002343 [1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4],
  certificateFrom 1010503 [1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5],
  certificateFrom 1021095 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 6],
  certificateFrom 1045735 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5],
  certificateFrom 1049831 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5],
  certificateFrom 1052743 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 5],
  certificateFrom 1058023 [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5],
  certificateFrom 1062759 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5],
  certificateFrom 1065063 [1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4],
  certificateFrom 1073895 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6],
  certificateFrom 1077991 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6],
  certificateFrom 1081511 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 5],
  certificateFrom 1082087 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4],
  certificateFrom 1103207 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4],
  certificateFrom 1107303 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4],
  certificateFrom 1113191 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7],
  certificateFrom 1115495 [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4],
  certificateFrom 1121383 [1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5],
  certificateFrom 1134247 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 6],
  certificateFrom 1143623 [1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4],
  certificateFrom 1158887 [1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5],
  certificateFrom 1178215 [1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4],
  certificateFrom 1191143 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6],
  certificateFrom 1194663 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 5],
  certificateFrom 1195879 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8],
  certificateFrom 1204071 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4],
  certificateFrom 1206343 [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 4],
  certificateFrom 1222823 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 6],
  certificateFrom 1234535 [1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5],
  certificateFrom 1235111 [1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 4],
  certificateFrom 1241575 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6],
  certificateFrom 1248583 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4],
  certificateFrom 1253863 [1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4],
  certificateFrom 1256775 [1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4],
  certificateFrom 1257383 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 5],
  certificateFrom 1265575 [1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 5],
  certificateFrom 1266791 [1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4],
  certificateFrom 1272039 [1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5],
  certificateFrom 1272679 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5],
  certificateFrom 1276775 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5],
  certificateFrom 1284967 [1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5],
  certificateFrom 1292007 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4],
  certificateFrom 1296103 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4],
  certificateFrom 1304295 [1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4],
  certificateFrom 1304903 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5],
  certificateFrom 1348263 [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 4],
  certificateFrom 1352423 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7],
  certificateFrom 1360615 [1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5],
  certificateFrom 1361735 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4],
  certificateFrom 1369927 [1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4],
  certificateFrom 1385831 [1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5],
  certificateFrom 1398695 [1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 4],
  certificateFrom 1413959 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5],
  certificateFrom 1418055 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5],
  certificateFrom 1426247 [1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5],
  certificateFrom 1432743 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 6],
  certificateFrom 1436839 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 6],
  certificateFrom 1440935 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 4],
  certificateFrom 1442119 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6],
  certificateFrom 1446215 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6],
  certificateFrom 1450311 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4],
  certificateFrom 1468519 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6],
  certificateFrom 1480807 [1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4],
  certificateFrom 1489639 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8],
  certificateFrom 1493735 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6],
  certificateFrom 1497831 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4],
  certificateFrom 1514855 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6],
  certificateFrom 1523047 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4],
  certificateFrom 1527111 [1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5],
  certificateFrom 1537127 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5],
  certificateFrom 1541223 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5],
  certificateFrom 1549415 [1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5],
  certificateFrom 1559367 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6],
  certificateFrom 1574631 [1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5],
  certificateFrom 1591655 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5],
  certificateFrom 1602791 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6],
  certificateFrom 1606887 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6],
  certificateFrom 1609799 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 6],
  certificateFrom 1610983 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4],
  certificateFrom 1615719 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8],
  certificateFrom 1616807 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 4],
  certificateFrom 1619815 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6],
  certificateFrom 1622087 [1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 4],
  certificateFrom 1623911 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4],
  certificateFrom 1624999 [1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 4],
  certificateFrom 1638567 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 6],
  certificateFrom 1640263 [1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5],
  certificateFrom 1650855 [1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 4],
  certificateFrom 1654375 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5],
  certificateFrom 1660231 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4],
  certificateFrom 1662567 [1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5],
  certificateFrom 1664327 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4],
  certificateFrom 1669031 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 5],
  certificateFrom 1672519 [1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4],
  certificateFrom 1673127 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 5],
  certificateFrom 1673703 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4],
  certificateFrom 1681319 [1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 5],
  certificateFrom 1681895 [1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4],
  certificateFrom 1692519 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5],
  certificateFrom 1711271 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 7],
  certificateFrom 1719463 [1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 5],
  certificateFrom 1720647 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7],
  certificateFrom 1728839 [1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5],
  certificateFrom 1745255 [1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4],
  certificateFrom 1751719 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 6],
  certificateFrom 1764007 [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 4],
  certificateFrom 1793383 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7],
  certificateFrom 1795687 [1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4],
  certificateFrom 1801575 [1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5],
  certificateFrom 1814439 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 6],
  certificateFrom 1829735 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6],
  certificateFrom 1833831 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6],
  certificateFrom 1837927 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4],
  certificateFrom 1857863 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8],
  certificateFrom 1861959 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6],
  certificateFrom 1866055 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4],
  certificateFrom 1881319 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7],
  certificateFrom 1889511 [1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5],
  certificateFrom 1895335 [1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 5],
  certificateFrom 1900647 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4],
  certificateFrom 1908839 [1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4],
  certificateFrom 1917095 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 7],
  certificateFrom 1921191 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 5],
  certificateFrom 1942855 [1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5],
  certificateFrom 1946983 [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4],
  certificateFrom 1952231 [1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5],
  certificateFrom 1956967 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5],
  certificateFrom 1971015 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6],
  certificateFrom 1975111 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6],
  certificateFrom 1979207 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4],
  certificateFrom 1994471 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5],
  certificateFrom 2002663 [1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5],
  certificateFrom 2013799 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4],
  certificateFrom 2021991 [1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4],
  certificateFrom 2041927 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 4],
  certificateFrom 2050119 [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 4],
  certificateFrom 2066023 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5],
  certificateFrom 2066599 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 4],
  certificateFrom 2070119 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5],
  certificateFrom 2070695 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 4],
  certificateFrom 2078311 [1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5],
  certificateFrom 2078887 [1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 4],
  certificateFrom 2085351 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4],
  certificateFrom 2089447 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4],
  certificateFrom 2094183 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6],
  certificateFrom 2097639 [1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4],
  certificateFrom 2098279 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6],
  certificateFrom 2102375 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4],
  certificateFrom 2107623 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5],
  certificateFrom 2108263 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7],
  certificateFrom 2115815 [1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5],
  certificateFrom 2116455 [1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5],
  certificateFrom 2135783 [1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4],
  certificateFrom 2148711 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6],
  certificateFrom 2160999 [1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4],
  certificateFrom 2179175 [1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5],
  certificateFrom 2183847 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 4],
  certificateFrom 2192039 [1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 4],
  certificateFrom 2196199 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5],
  certificateFrom 2211431 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6],
  certificateFrom 2217319 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5],
  certificateFrom 2221415 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5],
  certificateFrom 2226087 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 6],
  certificateFrom 2229607 [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5],
  certificateFrom 2230183 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 6],
  certificateFrom 2234279 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 4],
  certificateFrom 2245479 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8],
  certificateFrom 2249543 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7],
  certificateFrom 2249575 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6],
  certificateFrom 2253671 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4],
  certificateFrom 2257735 [1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5],
  certificateFrom 2292327 [1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5],
  certificateFrom 2311655 [1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4],
  certificateFrom 2312295 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4],
  certificateFrom 2314087 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9],
  certificateFrom 2316391 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4],
  certificateFrom 2318183 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5],
  certificateFrom 2320455 [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 5],
  certificateFrom 2324583 [1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4],
  certificateFrom 2337511 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4],
  certificateFrom 2349223 [1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 5],
  certificateFrom 2362695 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5],
  certificateFrom 2367975 [1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5],
  certificateFrom 2370887 [1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5],
  certificateFrom 2372711 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7],
  certificateFrom 2380903 [1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5],
  certificateFrom 2406119 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5],
  certificateFrom 2410215 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5],
  certificateFrom 2418407 [1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5],
  certificateFrom 2453575 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 4],
  certificateFrom 2457671 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 4],
  certificateFrom 2462375 [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 5],
  certificateFrom 2463591 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4],
  certificateFrom 2465863 [1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 4],
  certificateFrom 2475847 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5],
  certificateFrom 2478247 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 6],
  certificateFrom 2484039 [1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5],
  certificateFrom 2486439 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 4],
  certificateFrom 2504007 [1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4],
  certificateFrom 2504615 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 7],
  certificateFrom 2509927 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8],
  certificateFrom 2512807 [1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 5],
  certificateFrom 2514023 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6],
  certificateFrom 2518119 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4],
  certificateFrom 2551527 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6],
  certificateFrom 2555047 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 5],
  certificateFrom 2564423 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5],
  certificateFrom 2580839 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4],
  certificateFrom 2589031 [1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4],
  certificateFrom 2594919 [1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5],
  certificateFrom 2595495 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 4],
  certificateFrom 2599591 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 4],
  certificateFrom 2607783 [1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 4],
  certificateFrom 2611943 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5],
  certificateFrom 2623079 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6],
  certificateFrom 2627175 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6],
  certificateFrom 2631271 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4],
  certificateFrom 2637159 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5],
  certificateFrom 2664679 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6],
  certificateFrom 2679879 [1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 4],
  certificateFrom 2705735 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4],
  certificateFrom 2708647 [1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 4],
  certificateFrom 2725095 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5],
  certificateFrom 2730919 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 5],
  certificateFrom 2736199 [1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 5],
  certificateFrom 2738023 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5],
  certificateFrom 2739111 [1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 5],
  certificateFrom 2753255 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6],
  certificateFrom 2756775 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 7],
  certificateFrom 2764967 [1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 5],
  certificateFrom 2765543 [1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4],
  certificateFrom 2774343 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5],
  certificateFrom 2774375 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6],
  certificateFrom 2778439 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5],
  certificateFrom 2778471 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6],
  certificateFrom 2782567 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4],
  certificateFrom 2786631 [1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5],
  certificateFrom 2787815 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5],
  certificateFrom 2796007 [1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5],
  certificateFrom 2821799 [1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 4],
  certificateFrom 2859367 [1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5],
  certificateFrom 2875239 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6],
  certificateFrom 2878119 [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 5],
  certificateFrom 2878695 [1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4],
  certificateFrom 2901607 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7],
  certificateFrom 2909799 [1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5],
  certificateFrom 2910375 [1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 4],
  certificateFrom 2919751 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6],
  certificateFrom 2929127 [1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4],
  certificateFrom 2952039 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5],
  certificateFrom 2963175 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6],
  certificateFrom 2967271 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6],
  certificateFrom 2971367 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4],
  certificateFrom 2980167 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5],
  certificateFrom 2992487 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4],
  certificateFrom 2996583 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4],
  certificateFrom 3004775 [1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4],
  certificateFrom 3014759 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5],
  certificateFrom 3022951 [1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5],
  certificateFrom 3032903 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6],
  certificateFrom 3052903 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7],
  certificateFrom 3061095 [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5],
  certificateFrom 3093319 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5],
  certificateFrom 3093351 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4],
  certificateFrom 3112103 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 6],
  certificateFrom 3121479 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6],
  certificateFrom 3124391 [1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 4],
  certificateFrom 3127911 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5],
  certificateFrom 3133767 [1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4],
  certificateFrom 3136103 [1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5],
  certificateFrom 3147239 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4],
  certificateFrom 3153767 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7],
  certificateFrom 3155431 [1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4],
  certificateFrom 3156039 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 5],
  certificateFrom 3156071 [1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4],
  certificateFrom 3164231 [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 5],
  certificateFrom 3168999 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6],
  certificateFrom 3180711 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 5],
  certificateFrom 3181287 [1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4],
  certificateFrom 3184807 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 5],
  certificateFrom 3190119 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8],
  certificateFrom 3192999 [1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 5],
  certificateFrom 3194215 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6],
  certificateFrom 3198311 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4],
  certificateFrom 3199463 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5],
  certificateFrom 3203559 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5],
  certificateFrom 3211751 [1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5],
  certificateFrom 3216487 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5],
  certificateFrom 3241703 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7],
  certificateFrom 3246919 [1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4],
  certificateFrom 3249895 [1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5],
  certificateFrom 3275111 [1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5],
  certificateFrom 3282151 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6],
  certificateFrom 3287975 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 6],
  certificateFrom 3294439 [1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4],
  certificateFrom 3295079 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6],
  certificateFrom 3297351 [1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 4],
  certificateFrom 3297959 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 5],
  certificateFrom 3306151 [1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 5],
  certificateFrom 3307367 [1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4],
  certificateFrom 3331399 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6],
  certificateFrom 3335495 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6],
  certificateFrom 3339591 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4],
  certificateFrom 3344871 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6],
  certificateFrom 3348391 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 5],
  certificateFrom 3357799 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4],
  certificateFrom 3367783 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5],
  certificateFrom 3425767 [1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5],
  certificateFrom 3426407 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5],
  certificateFrom 3430503 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5],
  certificateFrom 3438695 [1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5],
  certificateFrom 3439271 [1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 4],
  certificateFrom 3447527 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7],
  certificateFrom 3451623 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5],
  certificateFrom 3501991 [1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 4],
  certificateFrom 3509095 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6],
  certificateFrom 3515463 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 4],
  certificateFrom 3521383 [1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4],
  certificateFrom 3523655 [1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 4],
  certificateFrom 3537223 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6],
  certificateFrom 3544231 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 4],
  certificateFrom 3549511 [1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4],
  certificateFrom 3552423 [1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 4],
  certificateFrom 3567687 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 5],
  certificateFrom 3571783 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 5],
  certificateFrom 3571815 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6],
  certificateFrom 3573607 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7],
  certificateFrom 3577703 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5],
  certificateFrom 3579975 [1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 5],
  certificateFrom 3597031 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4],
  certificateFrom 3600551 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 5],
  certificateFrom 3601127 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4],
  certificateFrom 3609319 [1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4],
  certificateFrom 3609927 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7],
  certificateFrom 3618119 [1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5],
  certificateFrom 3632231 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5],
  certificateFrom 3650375 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6],
  certificateFrom 3657383 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 4],
  certificateFrom 3662663 [1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4],
  certificateFrom 3665575 [1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 4],
  certificateFrom 3684967 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6],
  certificateFrom 3694951 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5],
  certificateFrom 3703143 [1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5],
  certificateFrom 3709607 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 5],
  certificateFrom 3713095 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 6],
  certificateFrom 3713703 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 5],
  certificateFrom 3714279 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4],
  certificateFrom 3721895 [1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 5],
  certificateFrom 3722471 [1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4],
  certificateFrom 3737767 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 6],
  certificateFrom 3741863 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 6],
  certificateFrom 3745383 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5],
  certificateFrom 3745959 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 4],
  certificateFrom 3756519 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6],
  certificateFrom 3760615 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6],
  certificateFrom 3764711 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4],
  certificateFrom 3773543 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6],
  certificateFrom 3785831 [1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4],
  certificateFrom 3793991 [1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 5],
  certificateFrom 3815751 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7],
  certificateFrom 3819847 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5],
  certificateFrom 3822759 [1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 5],
  certificateFrom 3836263 [1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4],
  certificateFrom 3855015 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 6],
  certificateFrom 3879655 [1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5],
  certificateFrom 3896679 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5],
  certificateFrom 3898983 [1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4],
  certificateFrom 3905447 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 6],
  certificateFrom 3917735 [1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 4],
  certificateFrom 3924839 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6],
  certificateFrom 3935911 [1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 5],
  certificateFrom 3937127 [1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4],
  certificateFrom 3955879 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 4],
  certificateFrom 3959975 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 4],
  certificateFrom 3965255 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4],
  certificateFrom 3968167 [1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 4],
  certificateFrom 3969351 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4],
  certificateFrom 3977543 [1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4],
  certificateFrom 3983463 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6],
  certificateFrom 3987559 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6],
  certificateFrom 3991655 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4],
  certificateFrom 3992807 [1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5],
  certificateFrom 4008679 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6],
  certificateFrom 4016295 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 7],
  certificateFrom 4016871 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4],
  certificateFrom 4024487 [1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 5],
  certificateFrom 4035047 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7],
  certificateFrom 4037991 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4],
  certificateFrom 4043239 [1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5],
  certificateFrom 4082503 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4],
  certificateFrom 4085479 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5],
  certificateFrom 4090695 [1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4],
  certificateFrom 4106599 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5],
  certificateFrom 4110695 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5],
  certificateFrom 4118887 [1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5],
  certificateFrom 4124743 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 6],
  certificateFrom 4125927 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4],
  certificateFrom 4128839 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 6],
  certificateFrom 4130023 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4],
  certificateFrom 4132935 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 4],
  certificateFrom 4134759 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6],
  certificateFrom 4138215 [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4],
  certificateFrom 4142951 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4],
  certificateFrom 4153511 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 8],
  certificateFrom 4157607 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 6],
  certificateFrom 4161703 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 4],
  certificateFrom 4189287 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6]]

theorem certificates_checked : ∀ c ∈ certificates, Accepted c := by
  decide +kernel

theorem coverage : (certificates.map Certificate.residue).toFinset =
    syracuseSevenMod32New22Step12Classes := by
  decide +kernel

end Session67Parents

theorem solution (n : ℕ)
    (h : n % 4194304 ∈ syracuseSevenMod32New22Step12Classes) :
    syracuseStep^[12] n < n := by
  rw [← Session67Parents.coverage] at h
  exact Session67Parents.Batch.descent_of_mem Session67Parents.certificates
    Session67Parents.certificates_checked n (List.mem_toFinset.mp h)

#print axioms Session67Parents.certificates_checked
#print axioms solution
