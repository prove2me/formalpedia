-- Prove2me | solution 1 for syracuse_descent_new25_step12_chunk01_seven_mod32
-- status  : ACCEPTED   (prove)
-- author  : @FakeMink
-- created : 2026-10-01T17:27:53.155266+00:00
-- url     : https://prove2.me/submissions/b1ee15ba-8135-4e00-a43a-629ea3fa3593

import Definitions.Def_syracuseSevenMod32New25Step12Chunk01Classes
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
  Valid 33554432 c.residue c.endA c.endB c.trace ∧
  c.trace.length = 12 ∧ c.endA ≤ 33554432 ∧ c.endB < c.residue

instance (c : Certificate) : Decidable (Accepted c) := by
  unfold Accepted
  infer_instance

def residues (cs : List Certificate) : List ℕ := cs.map Certificate.residue

theorem descent_of_accepted {c : Certificate} (h : Accepted c) (k : ℕ) :
    syracuseStep^[12] (33554432 * k + c.residue) < 33554432 * k + c.residue := by
  rcases h with ⟨hvalid, hlength, ha, hb⟩
  simpa only [hlength] using AffineTrace.strict_descent hvalid ha hb k

theorem descent_of_residue {c : Certificate} (h : Accepted c)
    (n : ℕ) (hn : n % 33554432 = c.residue) : syracuseStep^[12] n < n := by
  have hform : n = 33554432 * (n / 33554432) + c.residue := by omega
  rw [hform]
  exact descent_of_accepted h (n / 33554432)

/-- The proof consumes finite, kernel-checked certificate acceptance, not search output. -/
theorem descent_of_mem (cs : List Certificate) (hchecked : ∀ c ∈ cs, Accepted c)
    (n : ℕ) (h : n % 33554432 ∈ residues cs) : syracuseStep^[12] n < n := by
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
  let result := traceFrom 33554432 r es
  ⟨r, result.1, result.2.1, result.2.2⟩

def certificates : List Certificate :=
[  certificateFrom 215143 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 7],
  certificateFrom 273735 [1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 8],
  certificateFrom 308967 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 8],
  certificateFrom 365223 [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 8],
  certificateFrom 407463 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 10],
  certificateFrom 416871 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 9],
  certificateFrom 454375 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 9],
  certificateFrom 491879 [1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 7],
  certificateFrom 510631 [1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 7],
  certificateFrom 534119 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 7],
  certificateFrom 627943 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 8],
  certificateFrom 641959 [1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 8],
  certificateFrom 656103 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 9],
  certificateFrom 677191 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 8],
  certificateFrom 778087 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 9],
  certificateFrom 822599 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 9],
  certificateFrom 895335 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 7],
  certificateFrom 996167 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 8],
  certificateFrom 1024327 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 9],
  certificateFrom 1050087 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 7],
  certificateFrom 1087655 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 8],
  certificateFrom 1097063 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 9],
  certificateFrom 1106407 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 8],
  certificateFrom 1190823 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 9],
  certificateFrom 1270631 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 8],
  certificateFrom 1350375 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 10],
  certificateFrom 1418311 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 7],
  certificateFrom 1474631 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 8],
  certificateFrom 1718599 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 10],
  certificateFrom 1725607 [1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 8],
  certificateFrom 1871015 [1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 7],
  certificateFrom 1894503 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 7],
  certificateFrom 1927335 [1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 8],
  certificateFrom 1946087 [1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 8],
  certificateFrom 1988327 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 8],
  certificateFrom 2110311 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 8],
  certificateFrom 2190055 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 10],
  certificateFrom 2255719 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 7],
  certificateFrom 2314311 [1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 8],
  certificateFrom 2356551 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 8],
  certificateFrom 2448039 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 10],
  certificateFrom 2532455 [1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 7],
  certificateFrom 2558279 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 10],
  certificateFrom 2574695 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 7],
  certificateFrom 2626279 [1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 8],
  certificateFrom 2682535 [1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 8],
  certificateFrom 2994503 [1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 8],
  certificateFrom 3053159 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 7],
  certificateFrom 3090663 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 7],
  certificateFrom 3146983 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 8],
  certificateFrom 3175143 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 9],
  certificateFrom 3212647 [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 7],
  certificateFrom 3231399 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 9],
  certificateFrom 3362727 [1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 8],
  certificateFrom 3458887 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 7],
  certificateFrom 3515207 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 8],
  certificateFrom 3543367 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 9],
  certificateFrom 3766183 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 8],
  certificateFrom 3770855 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 7],
  certificateFrom 3789671 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 8],
  certificateFrom 3808423 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 10],
  certificateFrom 3892839 [1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 7],
  certificateFrom 3911591 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 9],
  certificateFrom 3935079 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 7],
  certificateFrom 3986663 [1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 8],
  certificateFrom 4139079 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 7],
  certificateFrom 4354887 [1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 8],
  certificateFrom 4408807 [1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 7],
  certificateFrom 4413543 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 7],
  certificateFrom 4446375 [1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 8],
  certificateFrom 4465127 [1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 8],
  certificateFrom 4469863 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 10],
  certificateFrom 4507367 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 8],
  certificateFrom 4615271 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 7],
  certificateFrom 4709095 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 8],
  certificateFrom 4777031 [1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 7],
  certificateFrom 4833351 [1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 8],
  certificateFrom 4875591 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 8],
  certificateFrom 5077319 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 8],
  certificateFrom 5093735 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 7],
  certificateFrom 5150055 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 10],
  certificateFrom 5225063 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 8],
  certificateFrom 5253223 [1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 7],
  certificateFrom 5295463 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 7],
  certificateFrom 5347047 [1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 8],
  certificateFrom 5403303 [1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 8],
  certificateFrom 5445543 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 8],
  certificateFrom 5454951 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 7],
  certificateFrom 5548775 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 8],
  certificateFrom 5670759 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 10],
  certificateFrom 5694183 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 7],
  certificateFrom 5715271 [1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 8],
  certificateFrom 5806759 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 8],
  certificateFrom 5811431 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 7],
  certificateFrom 5834919 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 9],
  certificateFrom 5853671 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 9],
  certificateFrom 5916999 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 8],
  certificateFrom 5933415 [1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 7],
  certificateFrom 5952167 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 9],
  certificateFrom 6062407 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 7],
  certificateFrom 6135143 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 7],
  certificateFrom 6179655 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 7],
  certificateFrom 6221895 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 9],
  certificateFrom 6411879 [1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 7],
  certificateFrom 6449383 [1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 7],
  certificateFrom 6454119 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 7],
  certificateFrom 6505703 [1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 8],
  certificateFrom 6510439 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 10],
  certificateFrom 6763687 [1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 8],
  certificateFrom 6817607 [1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 7],
  certificateFrom 6873927 [1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 8],
  certificateFrom 7129575 [1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 7],
  certificateFrom 7134311 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 7],
  certificateFrom 7148391 [1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 8],
  certificateFrom 7167143 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 8],
  certificateFrom 7171815 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 7],
  certificateFrom 7228135 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 8],
  certificateFrom 7293799 [1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 7],
  certificateFrom 7312551 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 9],
  certificateFrom 7373543 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 7],
  certificateFrom 7486119 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 8],
  certificateFrom 7495527 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 7],
  certificateFrom 7497799 [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 7],
  certificateFrom 7514279 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 9],
  certificateFrom 7533031 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 9],
  certificateFrom 7540039 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 7],
  certificateFrom 7596359 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 8],
  certificateFrom 7741767 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 7],
  certificateFrom 7772263 [1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 7],
  certificateFrom 7814503 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 7],
  certificateFrom 7828583 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 8],
  certificateFrom 7866087 [1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 8],
  certificateFrom 7894247 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 9],
  certificateFrom 7901255 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 9],
  certificateFrom 7908263 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 7],
  certificateFrom 7945831 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 8],
  certificateFrom 7964583 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 8],
  certificateFrom 8208551 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 10],
  certificateFrom 8234311 [1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 8],
  certificateFrom 8262471 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 9],
  certificateFrom 8452455 [1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 7],
  certificateFrom 8508775 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 8],
  certificateFrom 8536935 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 11],
  certificateFrom 8583783 [1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 8],
  certificateFrom 8804263 [1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 8],
  certificateFrom 8846503 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 8],
  certificateFrom 9029479 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 8],
  certificateFrom 9048231 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 10],
  certificateFrom 9170151 [1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 7],
  certificateFrom 9254631 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 9],
  certificateFrom 9306215 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 8],
  certificateFrom 9446887 [1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 7],
  certificateFrom 9484455 [1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 8],
  certificateFrom 9503207 [1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 8],
  certificateFrom 9507943 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 8],
  certificateFrom 9538375 [1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 7],
  certificateFrom 9573607 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 9],
  certificateFrom 9622855 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 9],
  certificateFrom 9812839 [1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 7],
  certificateFrom 9815111 [1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 7],
  certificateFrom 9869159 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 8],
  certificateFrom 9871431 [1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 8],
  certificateFrom 9892583 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 7],
  certificateFrom 9941831 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 9],
  certificateFrom 9948839 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 7],
  certificateFrom 9986407 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 8],
  certificateFrom 10005159 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 8],
  certificateFrom 10033319 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 9],
  certificateFrom 10052071 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 9],
  certificateFrom 10188135 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 8],
  certificateFrom 10216295 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 9],
  certificateFrom 10260807 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 7],
  certificateFrom 10420295 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 9],
  certificateFrom 10493031 [1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 7],
  certificateFrom 10530535 [1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 7],
  certificateFrom 10586855 [1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 8],
  certificateFrom 10629031 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 7],
  certificateFrom 10732263 [1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 7],
  certificateFrom 10844839 [1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 8],
  certificateFrom 10898759 [1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 7],
  certificateFrom 10933991 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 9],
  certificateFrom 10955079 [1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 8],
  certificateFrom 11055975 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 9],
  certificateFrom 11100487 [1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 7],
  certificateFrom 11173223 [1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 7],
  certificateFrom 11266983 [1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 7],
  certificateFrom 11302215 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 9],
  certificateFrom 11304551 [1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 8],
  certificateFrom 11323303 [1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 8],
  certificateFrom 11365543 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 8],
  certificateFrom 11449959 [1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 7],
  certificateFrom 11487463 [1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 7],
  certificateFrom 11543783 [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 8],
  certificateFrom 11548519 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 8],
  certificateFrom 11567271 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 8],
  certificateFrom 11855687 [1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 7],
  certificateFrom 11912007 [1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 8],
  certificateFrom 11975399 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 11],
  certificateFrom 12026983 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 8],
  certificateFrom 12092647 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 9],
  certificateFrom 12167655 [1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 7],
  certificateFrom 12205223 [1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 8],
  certificateFrom 12343623 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 11],
  certificateFrom 12406951 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 8],
  certificateFrom 12460871 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 9],
  certificateFrom 12535879 [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 7],
  certificateFrom 12552359 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 7],
  certificateFrom 12571111 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 7],
  certificateFrom 12664935 [1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 8],
  certificateFrom 12669607 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 7],
  certificateFrom 12707175 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 8],
  certificateFrom 12711847 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 9],
  certificateFrom 12735335 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 9],
  certificateFrom 12810343 [1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 7],
  certificateFrom 12866663 [1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 8],
  certificateFrom 12904167 [1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 8],
  certificateFrom 12939335 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 7],
  certificateFrom 13251303 [1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 7],
  certificateFrom 13272391 [1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 8],
  certificateFrom 13307559 [1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 7],
  certificateFrom 13345127 [1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 8],
  certificateFrom 13363879 [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 8],
  certificateFrom 13387367 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 10],
  certificateFrom 13453031 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 9],
  certificateFrom 13490535 [1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 7],
  certificateFrom 13546855 [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 8],
  certificateFrom 13619527 [1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 7],
  certificateFrom 13621863 [1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 8],
  certificateFrom 13654759 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 9],
  certificateFrom 13821255 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 9],
  certificateFrom 13987751 [1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 7],
  certificateFrom 14022983 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 9],
  certificateFrom 14029991 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 7],
  certificateFrom 14086311 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 8],
  certificateFrom 14170727 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 9],
  certificateFrom 14208231 [1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 7],
  certificateFrom 14231719 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 7],
  certificateFrom 14250471 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 7],
  certificateFrom 14391207 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 9],
  certificateFrom 14494439 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 9],
  certificateFrom 14576455 [1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 7],
  certificateFrom 14611687 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 7],
  certificateFrom 14618695 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 7],
  certificateFrom 14724263 [1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 8],
  certificateFrom 14747751 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 10],
  certificateFrom 14752423 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 9],
  certificateFrom 14850919 [1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 7],
  certificateFrom 14862663 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 9],
  certificateFrom 14907239 [1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 8],
  certificateFrom 14979911 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 7],
  certificateFrom 15385703 [1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 8],
  certificateFrom 15427943 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 10],
  certificateFrom 15568615 [1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 7],
  certificateFrom 15936839 [1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 7],
  certificateFrom 15972071 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 7],
  certificateFrom 16028327 [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 7],
  certificateFrom 16065895 [1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 8],
  certificateFrom 16112807 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 9],
  certificateFrom 16173799 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 9],
  certificateFrom 16291047 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 7],
  certificateFrom 16295783 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 11],
  certificateFrom 16305063 [1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 7],
  certificateFrom 16340295 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 7],
  certificateFrom 16342631 [1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 8],
  certificateFrom 16361383 [1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 8],
  certificateFrom 16431783 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 9],
  certificateFrom 16542023 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 9],
  certificateFrom 16659271 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 7],
  certificateFrom 16746087 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 8],
  certificateFrom 16750759 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 7],
  certificateFrom 16769511 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 7],
  certificateFrom 16774247 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 9],
  certificateFrom 16788327 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 10],
  certificateFrom 16891495 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 9],
  certificateFrom 16910247 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 9],
  certificateFrom 16933735 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 7],
  certificateFrom 17137735 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 7],
  certificateFrom 17388711 [1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 7],
  certificateFrom 17445031 [1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 8],
  certificateFrom 17454439 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 9],
  certificateFrom 17590439 [1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 7],
  certificateFrom 17609191 [1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 7],
  certificateFrom 17651431 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 7],
  certificateFrom 17703015 [1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 8],
  certificateFrom 17773415 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 7],
  certificateFrom 17792167 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 9],
  certificateFrom 17975143 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 9],
  certificateFrom 17977415 [1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 7],
  certificateFrom 18019655 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 7],
  certificateFrom 18106471 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 8],
  certificateFrom 18251879 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 9],
  certificateFrom 18289383 [1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 7],
  certificateFrom 18345639 [1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 7],
  certificateFrom 18383207 [1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 8],
  certificateFrom 18401959 [1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 8],
  certificateFrom 18425447 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 8],
  certificateFrom 18453607 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 9],
  certificateFrom 18657607 [1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 7],
  certificateFrom 18786663 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 8],
  certificateFrom 18810087 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 7],
  certificateFrom 18814823 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 9],
  certificateFrom 18833575 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 11],
  certificateFrom 18932071 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 9],
  certificateFrom 18941415 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 8],
  certificateFrom 18950823 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 9],
  certificateFrom 19025831 [1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 7],
  certificateFrom 19133799 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 9],
  certificateFrom 19147879 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 10],
  certificateFrom 19178311 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 7],
  certificateFrom 19309639 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 8],
  certificateFrom 19429287 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 7],
  certificateFrom 19452775 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 7],
  certificateFrom 19649767 [1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 7],
  certificateFrom 19762343 [1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 8],
  certificateFrom 19785831 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 8],
  certificateFrom 19828071 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 10],
  certificateFrom 19987559 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 10],
  certificateFrom 20017991 [1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 7],
  certificateFrom 20109479 [1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 7],
  certificateFrom 20128231 [1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 7],
  certificateFrom 20147047 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 8],
  certificateFrom 20170471 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 7],
  certificateFrom 20226791 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 10],
  certificateFrom 20311207 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 9],
  certificateFrom 20372199 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 7],
  certificateFrom 20423783 [1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 8],
  certificateFrom 20466023 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 8],
  certificateFrom 20494183 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 9],
  certificateFrom 20496455 [1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 7],
  certificateFrom 20512935 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 9],
  certificateFrom 20538695 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 7],
  certificateFrom 20595015 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 10],
  certificateFrom 20667751 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 10],
  certificateFrom 20740423 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 7],
  certificateFrom 20888167 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 7],
  certificateFrom 20944487 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 8],
  certificateFrom 20972647 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 9],
  certificateFrom 20981991 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 8],
  certificateFrom 21010151 [1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 7],
  certificateFrom 21066407 [1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 7],
  certificateFrom 21103975 [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 8],
  certificateFrom 21108647 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 7],
  certificateFrom 21188455 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 12],
  certificateFrom 21211879 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 7],
  certificateFrom 21350215 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 8],
  certificateFrom 21352615 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 9],
  certificateFrom 21378375 [1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 7],
  certificateFrom 21469863 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 7],
  certificateFrom 21580103 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 7],
  certificateFrom 21652839 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 9],
  certificateFrom 21662183 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 8],
  certificateFrom 21784167 [1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 8],
  certificateFrom 21826407 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 8],
  certificateFrom 22028135 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 10],
  certificateFrom 22030407 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 8],
  certificateFrom 22168807 [1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 7],
  certificateFrom 22300135 [1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 8],
  certificateFrom 22304871 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 8],
  certificateFrom 22426791 [1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 7],
  certificateFrom 22506599 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 8],
  certificateFrom 22537031 [1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 7],
  certificateFrom 22668359 [1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 8],
  certificateFrom 22811495 [1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 7],
  certificateFrom 22830247 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 7],
  certificateFrom 22891239 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 7],
  certificateFrom 22985063 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 8],
  certificateFrom 23031975 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 9],
  certificateFrom 23144551 [1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 8],
  certificateFrom 23149223 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 7],
  certificateFrom 23186791 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 8],
  certificateFrom 23259463 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 7],
  certificateFrom 23346279 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 8],
  certificateFrom 23491687 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 7],
  certificateFrom 23529191 [1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 7],
  certificateFrom 23585511 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 8],
  certificateFrom 23608935 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 7],
  certificateFrom 23627687 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 7],
  certificateFrom 23702759 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 8],
  certificateFrom 23824743 [1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 8],
  certificateFrom 23897415 [1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 7],
  certificateFrom 23953735 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 8],
  certificateFrom 24026471 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 8],
  certificateFrom 24070983 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 8],
  certificateFrom 24171879 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 7],
  certificateFrom 24246887 [1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 7],
  certificateFrom 24303207 [1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 8],
  certificateFrom 24340711 [1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 8],
  certificateFrom 24345447 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 8],
  certificateFrom 24467367 [1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 7],
  certificateFrom 24509607 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 7],
  certificateFrom 24692583 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 7],
  certificateFrom 24708935 [1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 8],
  certificateFrom 24969319 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 7],
  certificateFrom 25020903 [1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 8],
  certificateFrom 25025639 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 8],
  certificateFrom 25063143 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 8],
  certificateFrom 25147559 [1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 7],
  certificateFrom 25166311 [1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 7],
  certificateFrom 25171047 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 7],
  certificateFrom 25185127 [1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 8],
  certificateFrom 25264871 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 8],
  certificateFrom 25386855 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 8],
  certificateFrom 25389127 [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 8],
  certificateFrom 25431367 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 8],
  certificateFrom 25532263 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 7],
  certificateFrom 25534535 [1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 7],
  certificateFrom 25633095 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 8],
  certificateFrom 25649511 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 7],
  certificateFrom 25663591 [1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 8],
  certificateFrom 25668263 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 7],
  certificateFrom 25691751 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 9],
  certificateFrom 25705831 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 8],
  certificateFrom 25799591 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 8],
  certificateFrom 25851239 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 7],
  certificateFrom 26249959 [1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 7],
  certificateFrom 26343783 [1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 8],
  certificateFrom 26507943 [1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 7],
  certificateFrom 26618183 [1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 7],
  certificateFrom 26967655 [1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 7],
  certificateFrom 26986407 [1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 7],
  certificateFrom 27028647 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 7],
  certificateFrom 27052135 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 9],
  certificateFrom 27061479 [1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 8],
  certificateFrom 27084967 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 10],
  certificateFrom 27103719 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 10],
  certificateFrom 27206887 [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 7],
  certificateFrom 27211623 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 7],
  certificateFrom 27230375 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 7],
  certificateFrom 27338215 [1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 8],
  certificateFrom 27371111 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 9],
  certificateFrom 27429703 [1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 8],
  certificateFrom 27471943 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 10],
  certificateFrom 27575111 [1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 7],
  certificateFrom 27690087 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 7],
  certificateFrom 27704167 [1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 8],
  certificateFrom 27706439 [1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 8],
  certificateFrom 27732327 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 9],
  certificateFrom 27783911 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 8],
  certificateFrom 27840167 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 8],
  certificateFrom 27868327 [1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 7],
  certificateFrom 27887079 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 9],
  certificateFrom 28070055 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 7],
  certificateFrom 28152135 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 8],
  certificateFrom 28255303 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 9],
  certificateFrom 28328039 [1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 7],
  certificateFrom 28370279 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 7],
  certificateFrom 28384359 [1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 8],
  certificateFrom 28421863 [1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 8],
  certificateFrom 28520359 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 8],
  certificateFrom 28529767 [1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 7],
  certificateFrom 28567271 [1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 7],
  certificateFrom 28623591 [1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 8],
  certificateFrom 28731495 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 9],
  certificateFrom 28790087 [1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 8],
  certificateFrom 28935495 [1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 7],
  certificateFrom 28991815 [1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 8],
  certificateFrom 29008231 [1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 7],
  certificateFrom 29026983 [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 7],
  certificateFrom 29064551 [1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 8],
  certificateFrom 29092711 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 9],
  certificateFrom 29144295 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 10],
  certificateFrom 29158311 [1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 8],
  certificateFrom 29209959 [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 7],
  certificateFrom 29284967 [1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 7],
  certificateFrom 29341287 [1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 8],
  certificateFrom 29378791 [1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 8],
  certificateFrom 29411687 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 9],
  certificateFrom 29512519 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 10],
  certificateFrom 29747015 [1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 8],
  certificateFrom 29749415 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 7],
  certificateFrom 29772903 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 11],
  certificateFrom 29890151 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 9],
  certificateFrom 29927655 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 9],
  certificateFrom 30058983 [1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 8],
  certificateFrom 30295879 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 9],
  certificateFrom 30387367 [1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 7],
  certificateFrom 30427207 [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 8],
  certificateFrom 30443687 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 8],
  certificateFrom 30453095 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 11],
  certificateFrom 30462439 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 8],
  certificateFrom 30504679 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 10],
  certificateFrom 30560935 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 8],
  certificateFrom 30570343 [1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 7],
  certificateFrom 30607847 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 9],
  certificateFrom 30701671 [1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 8],
  certificateFrom 30772071 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 9],
  certificateFrom 30830663 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 8],
  certificateFrom 30872903 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 10],
  certificateFrom 30976071 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 9],
  certificateFrom 31048807 [1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 7],
  certificateFrom 31142631 [1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 8],
  certificateFrom 31198887 [1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 8],
  certificateFrom 31250535 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 9],
  certificateFrom 31381863 [1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 8],
  certificateFrom 31452263 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 9],
  certificateFrom 31466343 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 10],
  certificateFrom 31510855 [1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 8],
  certificateFrom 31728999 [1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 7],
  certificateFrom 31879079 [1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 8],
  certificateFrom 31921319 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 8],
  certificateFrom 31930727 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 9],
  certificateFrom 32005735 [1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 7],
  certificateFrom 32024487 [1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 7],
  certificateFrom 32099559 [1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 8],
  certificateFrom 32123047 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 8],
  certificateFrom 32132455 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 9],
  certificateFrom 32141799 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 8],
  certificateFrom 32291943 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 9],
  certificateFrom 32306023 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 10],
  certificateFrom 32409191 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 7],
  certificateFrom 32467783 [1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 8],
  certificateFrom 32503015 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 8],
  certificateFrom 32510023 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 8],
  certificateFrom 32531175 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 9],
  certificateFrom 32648423 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 9],
  certificateFrom 32653159 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 11],
  certificateFrom 32742247 [1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 8],
  certificateFrom 32871239 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 8],
  certificateFrom 32899399 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 9],
  certificateFrom 32972135 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 9],
  certificateFrom 33016647 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 9],
  certificateFrom 33108135 [1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 7],
  certificateFrom 33291111 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 9],
  certificateFrom 33366119 [1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 7],
  certificateFrom 33459943 [1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 8]]

theorem certificates_checked : ∀ c ∈ certificates, Accepted c := by
  decide +kernel

theorem coverage : (certificates.map Certificate.residue).toFinset =
    syracuseSevenMod32New25Step12Chunk01Classes := by
  decide +kernel

end Session67Parents

theorem solution (n : ℕ)
    (h : n % 33554432 ∈ syracuseSevenMod32New25Step12Chunk01Classes) :
    syracuseStep^[12] n < n := by
  rw [← Session67Parents.coverage] at h
  exact Session67Parents.Batch.descent_of_mem Session67Parents.certificates
    Session67Parents.certificates_checked n (List.mem_toFinset.mp h)

#print axioms Session67Parents.certificates_checked
#print axioms solution
