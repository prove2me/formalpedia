-- Prove2me | solution 1 for syracuse_descent_new24_step12_chunk01_seven_mod32
-- status  : ACCEPTED   (prove)
-- author  : @FakeMink
-- created : 2026-10-01T17:26:29.895411+00:00
-- url     : https://prove2.me/submissions/ba128ecb-6570-4a5d-a15f-19065357bf34

import Definitions.Def_syracuseSevenMod32New24Step12Chunk01Classes
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
  Valid 16777216 c.residue c.endA c.endB c.trace ∧
  c.trace.length = 12 ∧ c.endA ≤ 16777216 ∧ c.endB < c.residue

instance (c : Certificate) : Decidable (Accepted c) := by
  unfold Accepted
  infer_instance

def residues (cs : List Certificate) : List ℕ := cs.map Certificate.residue

theorem descent_of_accepted {c : Certificate} (h : Accepted c) (k : ℕ) :
    syracuseStep^[12] (16777216 * k + c.residue) < 16777216 * k + c.residue := by
  rcases h with ⟨hvalid, hlength, ha, hb⟩
  simpa only [hlength] using AffineTrace.strict_descent hvalid ha hb k

theorem descent_of_residue {c : Certificate} (h : Accepted c)
    (n : ℕ) (hn : n % 16777216 = c.residue) : syracuseStep^[12] n < n := by
  have hform : n = 16777216 * (n / 16777216) + c.residue := by omega
  rw [hform]
  exact descent_of_accepted h (n / 16777216)

/-- The proof consumes finite, kernel-checked certificate acceptance, not search output. -/
theorem descent_of_mem (cs : List Certificate) (hchecked : ∀ c ∈ cs, Accepted c)
    (n : ℕ) (h : n % 16777216 ∈ residues cs) : syracuseStep^[12] n < n := by
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
  let result := traceFrom 16777216 r es
  ⟨r, result.1, result.2.1, result.2.2⟩

def certificates : List Certificate :=
[  certificateFrom 487 [1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 6],
  certificateFrom 5223 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 6],
  certificateFrom 19303 [1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 7],
  certificateFrom 63847 [1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 6],
  certificateFrom 99047 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 7],
  certificateFrom 120167 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 7],
  certificateFrom 148327 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 10],
  certificateFrom 195175 [1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 7],
  certificateFrom 221031 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 7],
  certificateFrom 223303 [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 7],
  certificateFrom 265543 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 7],
  certificateFrom 366439 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 6],
  certificateFrom 368711 [1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 6],
  certificateFrom 415655 [1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 7],
  certificateFrom 457895 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 7],
  certificateFrom 467271 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 7],
  certificateFrom 483687 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 6],
  certificateFrom 497767 [1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 7],
  certificateFrom 502439 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 6],
  certificateFrom 525927 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 8],
  certificateFrom 540007 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 7],
  certificateFrom 633767 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 7],
  certificateFrom 640871 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 7],
  certificateFrom 659623 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 9],
  certificateFrom 685415 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 6],
  certificateFrom 781543 [1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 6],
  certificateFrom 866023 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 8],
  certificateFrom 917607 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 7],
  certificateFrom 1058279 [1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 6],
  certificateFrom 1084135 [1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 6],
  certificateFrom 1095847 [1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 7],
  certificateFrom 1114599 [1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 7],
  certificateFrom 1119335 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 7],
  certificateFrom 1149767 [1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 6],
  certificateFrom 1177959 [1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 7],
  certificateFrom 1184999 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 8],
  certificateFrom 1234247 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 8],
  certificateFrom 1342119 [1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 6],
  certificateFrom 1424231 [1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 6],
  certificateFrom 1426503 [1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 6],
  certificateFrom 1452359 [1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 6],
  certificateFrom 1480551 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 7],
  certificateFrom 1482823 [1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 7],
  certificateFrom 1503975 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 6],
  certificateFrom 1553223 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 8],
  certificateFrom 1560231 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 6],
  certificateFrom 1597799 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 7],
  certificateFrom 1616551 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 7],
  certificateFrom 1644711 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 8],
  certificateFrom 1663463 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 8],
  certificateFrom 1799527 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 7],
  certificateFrom 1801831 [1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 6],
  certificateFrom 1820583 [1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 6],
  certificateFrom 1827687 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 8],
  certificateFrom 1862823 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 6],
  certificateFrom 1872199 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 6],
  certificateFrom 1886311 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 8],
  certificateFrom 1895655 [1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 7],
  certificateFrom 1919143 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 9],
  certificateFrom 1937895 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 9],
  certificateFrom 2031687 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 8],
  certificateFrom 2041063 [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 6],
  certificateFrom 2045799 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 6],
  certificateFrom 2064551 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 6],
  certificateFrom 2104423 [1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 6],
  certificateFrom 2141927 [1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 6],
  certificateFrom 2172391 [1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 7],
  certificateFrom 2198247 [1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 7],
  certificateFrom 2205287 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 8],
  certificateFrom 2240423 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 6],
  certificateFrom 2263879 [1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 7],
  certificateFrom 2306119 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 9],
  certificateFrom 2343655 [1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 6],
  certificateFrom 2409287 [1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 6],
  certificateFrom 2456231 [1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 7],
  certificateFrom 2510151 [1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 6],
  certificateFrom 2524263 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 6],
  certificateFrom 2538343 [1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 7],
  certificateFrom 2540615 [1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 7],
  certificateFrom 2545383 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 8],
  certificateFrom 2566471 [1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 7],
  certificateFrom 2566503 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 8],
  certificateFrom 2618087 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 7],
  certificateFrom 2667367 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 8],
  certificateFrom 2674343 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 7],
  certificateFrom 2702503 [1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 6],
  certificateFrom 2711879 [1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 6],
  certificateFrom 2721255 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 8],
  certificateFrom 2784615 [1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 6],
  certificateFrom 2878375 [1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 6],
  certificateFrom 2904231 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 6],
  certificateFrom 2913607 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 8],
  certificateFrom 2915943 [1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 7],
  certificateFrom 2934695 [1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 7],
  certificateFrom 2976935 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 7],
  certificateFrom 2986311 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 7],
  certificateFrom 3061351 [1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 6],
  certificateFrom 3089479 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 8],
  certificateFrom 3098855 [1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 6],
  certificateFrom 3155175 [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 7],
  certificateFrom 3159911 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 7],
  certificateFrom 3162215 [1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 6],
  certificateFrom 3178663 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 7],
  certificateFrom 3204455 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 6],
  certificateFrom 3218535 [1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 7],
  certificateFrom 3256039 [1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 7],
  certificateFrom 3354535 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 7],
  certificateFrom 3363943 [1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 6],
  certificateFrom 3401447 [1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 6],
  certificateFrom 3457767 [1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 7],
  certificateFrom 3467079 [1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 6],
  certificateFrom 3523399 [1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 7],
  certificateFrom 3565671 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 8],
  certificateFrom 3586791 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 10],
  certificateFrom 3624263 [1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 7],
  certificateFrom 3638375 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 7],
  certificateFrom 3704039 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 8],
  certificateFrom 3769671 [1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 6],
  certificateFrom 3779047 [1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 6],
  certificateFrom 3816615 [1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 7],
  certificateFrom 3825991 [1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 7],
  certificateFrom 3842407 [1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 6],
  certificateFrom 3861159 [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 6],
  certificateFrom 3898727 [1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 7],
  certificateFrom 3926887 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 8],
  certificateFrom 3955015 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 10],
  certificateFrom 3978471 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 9],
  certificateFrom 3992487 [1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 7],
  certificateFrom 4018343 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 7],
  certificateFrom 4044135 [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 6],
  certificateFrom 4072263 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 8],
  certificateFrom 4119143 [1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 6],
  certificateFrom 4147271 [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 6],
  certificateFrom 4163751 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 6],
  certificateFrom 4175463 [1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 7],
  certificateFrom 4182503 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 6],
  certificateFrom 4212967 [1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 7],
  certificateFrom 4245863 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 8],
  certificateFrom 4276327 [1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 7],
  certificateFrom 4280999 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 6],
  certificateFrom 4318567 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 7],
  certificateFrom 4323239 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 8],
  certificateFrom 4346695 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 9],
  certificateFrom 4346727 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 8],
  certificateFrom 4421735 [1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 6],
  certificateFrom 4478055 [1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 7],
  certificateFrom 4515559 [1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 7],
  certificateFrom 4550727 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 6],
  certificateFrom 4581191 [1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 7],
  certificateFrom 4583591 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 6],
  certificateFrom 4607079 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 10],
  certificateFrom 4724327 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 8],
  certificateFrom 4761831 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 8],
  certificateFrom 4862695 [1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 6],
  certificateFrom 4883783 [1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 7],
  certificateFrom 4893159 [1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 7],
  certificateFrom 4918951 [1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 6],
  certificateFrom 4956519 [1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 7],
  certificateFrom 4975271 [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 7],
  certificateFrom 4998759 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 9],
  certificateFrom 5064423 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 8],
  certificateFrom 5101927 [1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 6],
  certificateFrom 5130055 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 8],
  certificateFrom 5158247 [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 7],
  certificateFrom 5221543 [1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 6],
  certificateFrom 5230919 [1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 6],
  certificateFrom 5233255 [1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 7],
  certificateFrom 5261383 [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 7],
  certificateFrom 5266151 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 8],
  certificateFrom 5277863 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 7],
  certificateFrom 5287271 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 10],
  certificateFrom 5296615 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 7],
  certificateFrom 5338855 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 9],
  certificateFrom 5395111 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 7],
  certificateFrom 5404519 [1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 6],
  certificateFrom 5432647 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 8],
  certificateFrom 5442023 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 8],
  certificateFrom 5535847 [1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 7],
  certificateFrom 5599143 [1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 6],
  certificateFrom 5606247 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 8],
  certificateFrom 5634375 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 8],
  certificateFrom 5641383 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 6],
  certificateFrom 5664839 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 7],
  certificateFrom 5697703 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 7],
  certificateFrom 5707079 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 9],
  certificateFrom 5782119 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 8],
  certificateFrom 5810247 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 8],
  certificateFrom 5819623 [1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 6],
  certificateFrom 5843111 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 6],
  certificateFrom 5861863 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 6],
  certificateFrom 5882983 [1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 6],
  certificateFrom 5976807 [1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 7],
  certificateFrom 6002599 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 8],
  certificateFrom 6033063 [1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 7],
  certificateFrom 6084711 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 8],
  certificateFrom 6105831 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 8],
  certificateFrom 6187847 [1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 6],
  certificateFrom 6216039 [1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 7],
  certificateFrom 6223079 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 6],
  certificateFrom 6230087 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 6],
  certificateFrom 6286439 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 8],
  certificateFrom 6300519 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 9],
  certificateFrom 6335655 [1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 7],
  certificateFrom 6345031 [1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 7],
  certificateFrom 6359143 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 9],
  certificateFrom 6363815 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 8],
  certificateFrom 6462311 [1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 6],
  certificateFrom 6474055 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 8],
  certificateFrom 6518631 [1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 7],
  certificateFrom 6563175 [1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 6],
  certificateFrom 6591303 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 6],
  certificateFrom 6713255 [1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 7],
  certificateFrom 6755495 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 7],
  certificateFrom 6764903 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 8],
  certificateFrom 6839911 [1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 6],
  certificateFrom 6858663 [1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 6],
  certificateFrom 6933735 [1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 7],
  certificateFrom 6957223 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 7],
  certificateFrom 6966631 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 8],
  certificateFrom 6975975 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 7],
  certificateFrom 6997095 [1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 7],
  certificateFrom 7039335 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 9],
  certificateFrom 7126119 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 8],
  certificateFrom 7140199 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 9],
  certificateFrom 7180007 [1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 6],
  certificateFrom 7243367 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 6],
  certificateFrom 7301959 [1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 7],
  certificateFrom 7337191 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 7],
  certificateFrom 7344199 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 7],
  certificateFrom 7365351 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 8],
  certificateFrom 7482599 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 8],
  certificateFrom 7487335 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 10],
  certificateFrom 7548231 [1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 6],
  certificateFrom 7576423 [1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 7],
  certificateFrom 7583463 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 6],
  certificateFrom 7639719 [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 6],
  certificateFrom 7677287 [1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 7],
  certificateFrom 7705415 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 7],
  certificateFrom 7724199 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 8],
  certificateFrom 7733575 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 8],
  certificateFrom 7785191 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 8],
  certificateFrom 7806311 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 8],
  certificateFrom 7850823 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 8],
  certificateFrom 7902439 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 6],
  certificateFrom 7907175 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 10],
  certificateFrom 7916455 [1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 6],
  certificateFrom 7942311 [1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 6],
  certificateFrom 7951687 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 6],
  certificateFrom 7954023 [1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 7],
  certificateFrom 7972775 [1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 7],
  certificateFrom 8043175 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 8],
  certificateFrom 8125287 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 8],
  certificateFrom 8153415 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 8],
  certificateFrom 8200295 [1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 6],
  certificateFrom 8270663 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 6],
  certificateFrom 8294119 [1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 7],
  certificateFrom 8357479 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 7],
  certificateFrom 8362151 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 6],
  certificateFrom 8380903 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 6],
  certificateFrom 8385639 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 8],
  certificateFrom 8399719 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 9],
  certificateFrom 8502887 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 8],
  certificateFrom 8521639 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 8],
  certificateFrom 8545127 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 6],
  certificateFrom 8603751 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 6],
  certificateFrom 8662343 [1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 7],
  certificateFrom 8697575 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 7],
  certificateFrom 8749127 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 6],
  certificateFrom 8753831 [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 7],
  certificateFrom 8796071 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 9],
  certificateFrom 8805479 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 8],
  certificateFrom 8842983 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 8],
  certificateFrom 8880487 [1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 6],
  certificateFrom 8899239 [1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 6],
  certificateFrom 8922727 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 6],
  certificateFrom 9000103 [1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 6],
  certificateFrom 9016551 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 7],
  certificateFrom 9030567 [1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 7],
  certificateFrom 9044711 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 8],
  certificateFrom 9056423 [1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 7],
  certificateFrom 9065799 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 7],
  certificateFrom 9065831 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 8],
  certificateFrom 9166695 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 8],
  certificateFrom 9201831 [1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 6],
  certificateFrom 9211207 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 8],
  certificateFrom 9220583 [1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 6],
  certificateFrom 9262823 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 6],
  certificateFrom 9283943 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 6],
  certificateFrom 9314407 [1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 7],
  certificateFrom 9384775 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 7],
  certificateFrom 9384807 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 6],
  certificateFrom 9403559 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 8],
  certificateFrom 9412935 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 8],
  certificateFrom 9438695 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 6],
  certificateFrom 9476263 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 7],
  certificateFrom 9485671 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 8],
  certificateFrom 9495015 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 7],
  certificateFrom 9579431 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 8],
  certificateFrom 9586535 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 8],
  certificateFrom 9588807 [1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 6],
  certificateFrom 9631047 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 6],
  certificateFrom 9659239 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 7],
  certificateFrom 9717863 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 7],
  certificateFrom 9738983 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 9],
  certificateFrom 9806919 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 6],
  certificateFrom 9863239 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 7],
  certificateFrom 9863271 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 8],
  certificateFrom 9900775 [1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 6],
  certificateFrom 9957031 [1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 6],
  certificateFrom 9994599 [1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 7],
  certificateFrom 10013351 [1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 7],
  certificateFrom 10036839 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 7],
  certificateFrom 10064999 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 8],
  certificateFrom 10107207 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 9],
  certificateFrom 10114215 [1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 7],
  certificateFrom 10259623 [1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 6],
  certificateFrom 10268999 [1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 6],
  certificateFrom 10283111 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 6],
  certificateFrom 10315943 [1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 7],
  certificateFrom 10334695 [1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 7],
  certificateFrom 10376935 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 7],
  certificateFrom 10398055 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 7],
  certificateFrom 10421479 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 6],
  certificateFrom 10426215 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 8],
  certificateFrom 10444967 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 10],
  certificateFrom 10498919 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 7],
  certificateFrom 10543463 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 8],
  certificateFrom 10552807 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 7],
  certificateFrom 10562215 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 8],
  certificateFrom 10578663 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 9],
  certificateFrom 10637223 [1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 6],
  certificateFrom 10644327 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 6],
  certificateFrom 10702919 [1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 7],
  certificateFrom 10745159 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 7],
  certificateFrom 10745191 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 8],
  certificateFrom 10759271 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 9],
  certificateFrom 10789703 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 6],
  certificateFrom 10836647 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 9],
  certificateFrom 10921031 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 7],
  certificateFrom 10921063 [1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 6],
  certificateFrom 10946887 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 9],
  certificateFrom 10963303 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 6],
  certificateFrom 11014887 [1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 7],
  certificateFrom 11040679 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 6],
  certificateFrom 11064167 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 6],
  certificateFrom 11071143 [1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 7],
  certificateFrom 11261159 [1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 6],
  certificateFrom 11373735 [1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 7],
  certificateFrom 11383111 [1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 7],
  certificateFrom 11397223 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 7],
  certificateFrom 11439463 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 9],
  certificateFrom 11441767 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 6],
  certificateFrom 11479271 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 6],
  certificateFrom 11535591 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 7],
  certificateFrom 11563751 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 8],
  certificateFrom 11598951 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 9],
  certificateFrom 11601255 [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 6],
  certificateFrom 11620007 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 8],
  certificateFrom 11629383 [1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 6],
  certificateFrom 11720871 [1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 6],
  certificateFrom 11739623 [1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 6],
  certificateFrom 11751335 [1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 7],
  certificateFrom 11758439 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 7],
  certificateFrom 11781863 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 6],
  certificateFrom 11838183 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 9],
  certificateFrom 11847495 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 6],
  certificateFrom 11903815 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 7],
  certificateFrom 11922599 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 8],
  certificateFrom 11931975 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 8],
  certificateFrom 11983591 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 6],
  certificateFrom 12035175 [1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 7],
  certificateFrom 12077415 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 7],
  certificateFrom 12105575 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 8],
  certificateFrom 12107847 [1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 6],
  certificateFrom 12124327 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 8],
  certificateFrom 12150087 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 6],
  certificateFrom 12154791 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 7],
  certificateFrom 12159463 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 6],
  certificateFrom 12178279 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 7],
  certificateFrom 12197031 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 9],
  certificateFrom 12206407 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 9],
  certificateFrom 12279143 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 9],
  certificateFrom 12281447 [1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 6],
  certificateFrom 12300199 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 8],
  certificateFrom 12323687 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 6],
  certificateFrom 12351815 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 6],
  certificateFrom 12375271 [1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 7],
  certificateFrom 12499559 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 6],
  certificateFrom 12527687 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 6],
  certificateFrom 12555879 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 7],
  certificateFrom 12584039 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 8],
  certificateFrom 12593383 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 7],
  certificateFrom 12621543 [1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 6],
  certificateFrom 12677799 [1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 6],
  certificateFrom 12715367 [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 7],
  certificateFrom 12720039 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 6],
  certificateFrom 12743495 [1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 7],
  certificateFrom 12797415 [1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 6],
  certificateFrom 12799847 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 11],
  certificateFrom 12802151 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 6],
  certificateFrom 12823271 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 6],
  certificateFrom 12834983 [1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 7],
  certificateFrom 12853735 [1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 7],
  certificateFrom 12858471 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 9],
  certificateFrom 12895975 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 7],
  certificateFrom 12961607 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 7],
  certificateFrom 12964007 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 8],
  certificateFrom 12989767 [1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 6],
  certificateFrom 13003879 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 6],
  certificateFrom 13081255 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 6],
  certificateFrom 13097703 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 7],
  certificateFrom 13165639 [1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 6],
  certificateFrom 13191495 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 6],
  certificateFrom 13221959 [1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 7],
  certificateFrom 13264199 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 7],
  certificateFrom 13264231 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 8],
  certificateFrom 13273575 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 7],
  certificateFrom 13395559 [1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 7],
  certificateFrom 13437799 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 7],
  certificateFrom 13465927 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 7],
  certificateFrom 13482343 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 6],
  certificateFrom 13538663 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 9],
  certificateFrom 13613671 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 7],
  certificateFrom 13639527 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 9],
  certificateFrom 13641799 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 7],
  certificateFrom 13641831 [1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 6],
  certificateFrom 13684071 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 6],
  certificateFrom 13735655 [1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 7],
  certificateFrom 13780199 [1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 6],
  certificateFrom 13791911 [1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 7],
  certificateFrom 13834151 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 7],
  certificateFrom 13843559 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 6],
  certificateFrom 13911527 [1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 7],
  certificateFrom 13916263 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 7],
  certificateFrom 13937383 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 7],
  certificateFrom 14038183 [1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 6],
  certificateFrom 14059367 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 9],
  certificateFrom 14082791 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 6],
  certificateFrom 14103879 [1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 7],
  certificateFrom 14117991 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 7],
  certificateFrom 14148423 [1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 6],
  certificateFrom 14195367 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 7],
  certificateFrom 14200039 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 6],
  certificateFrom 14223527 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 8],
  certificateFrom 14242279 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 8],
  certificateFrom 14279751 [1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 7],
  certificateFrom 14305607 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 7],
  certificateFrom 14322023 [1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 6],
  certificateFrom 14340775 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 8],
  certificateFrom 14422887 [1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 6],
  certificateFrom 14441639 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 6],
  certificateFrom 14451015 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 6],
  certificateFrom 14502631 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 6],
  certificateFrom 14523751 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 6],
  certificateFrom 14568263 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 6],
  certificateFrom 14596455 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 7],
  certificateFrom 14610503 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 8],
  certificateFrom 14643367 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 8],
  certificateFrom 14755943 [1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 7],
  certificateFrom 14760615 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 6],
  certificateFrom 14798183 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 7],
  certificateFrom 14800487 [1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 6],
  certificateFrom 14837991 [1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 6],
  certificateFrom 14842727 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 6],
  certificateFrom 14870855 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 6],
  certificateFrom 14894311 [1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 7],
  certificateFrom 14899047 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 9],
  certificateFrom 14957671 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 7],
  certificateFrom 15103079 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 6],
  certificateFrom 15140583 [1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 6],
  certificateFrom 15152295 [1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 7],
  certificateFrom 15196903 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 7],
  certificateFrom 15206215 [1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 6],
  certificateFrom 15220327 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 6],
  certificateFrom 15239079 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 6],
  certificateFrom 15262535 [1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 7],
  certificateFrom 15314151 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 7],
  certificateFrom 15436135 [1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 7],
  certificateFrom 15508807 [1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 6],
  certificateFrom 15518183 [1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 6],
  certificateFrom 15522919 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 6],
  certificateFrom 15536999 [1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 7],
  certificateFrom 15555751 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 7],
  certificateFrom 15560423 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 6],
  certificateFrom 15565127 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 7],
  certificateFrom 15616743 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 7],
  certificateFrom 15637863 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 7],
  certificateFrom 15682375 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 7],
  certificateFrom 15682407 [1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 6],
  certificateFrom 15701159 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 8],
  certificateFrom 15762151 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 6],
  certificateFrom 15783271 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 6],
  certificateFrom 15858279 [1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 6],
  certificateFrom 15874727 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 7],
  certificateFrom 15884135 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 6],
  certificateFrom 15886407 [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 6],
  certificateFrom 15902887 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 8],
  certificateFrom 15914599 [1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 7],
  certificateFrom 15921639 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 8],
  certificateFrom 15928647 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 6],
  certificateFrom 15952103 [1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 7],
  certificateFrom 15956839 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 7],
  certificateFrom 15984967 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 7],
  certificateFrom 16078759 [1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 6],
  certificateFrom 16120999 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 6],
  certificateFrom 16130375 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 6],
  certificateFrom 16160871 [1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 6],
  certificateFrom 16203111 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 6],
  certificateFrom 16217191 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 7],
  certificateFrom 16254695 [1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 7],
  certificateFrom 16282855 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 8],
  certificateFrom 16289863 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 8],
  certificateFrom 16296871 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 6],
  certificateFrom 16303975 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 6],
  certificateFrom 16320327 [1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 7],
  certificateFrom 16334439 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 7],
  certificateFrom 16353191 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 7],
  certificateFrom 16580711 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 6],
  certificateFrom 16597159 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 9],
  certificateFrom 16622919 [1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 7],
  certificateFrom 16632295 [1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 7],
  certificateFrom 16637031 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 7],
  certificateFrom 16651079 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 8],
  certificateFrom 16674535 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 7],
  certificateFrom 16758951 [1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 6]]

theorem certificates_checked : ∀ c ∈ certificates, Accepted c := by
  decide +kernel

theorem coverage : (certificates.map Certificate.residue).toFinset =
    syracuseSevenMod32New24Step12Chunk01Classes := by
  decide +kernel

end Session67Parents

theorem solution (n : ℕ)
    (h : n % 16777216 ∈ syracuseSevenMod32New24Step12Chunk01Classes) :
    syracuseStep^[12] n < n := by
  rw [← Session67Parents.coverage] at h
  exact Session67Parents.Batch.descent_of_mem Session67Parents.certificates
    Session67Parents.certificates_checked n (List.mem_toFinset.mp h)

#print axioms Session67Parents.certificates_checked
#print axioms solution
