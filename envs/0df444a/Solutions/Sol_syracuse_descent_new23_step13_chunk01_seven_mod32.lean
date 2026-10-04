-- Prove2me | solution 1 for syracuse_descent_new23_step13_chunk01_seven_mod32
-- status  : ACCEPTED   (prove)
-- author  : @FakeMink
-- created : 2026-10-02T19:20:40.076454+00:00
-- url     : https://prove2.me/submissions/27893f46-9cc0-438c-ae65-51a8e4b78821

import Definitions.Def_syracuseSevenMod32New23Step13Chunk01Classes
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

/-- Each accepted certificate proves 13-step descent on its entire progression. -/
def Accepted (c : Certificate) : Prop :=
  Valid 8388608 c.residue c.endA c.endB c.trace ∧
  c.trace.length = 13 ∧ c.endA ≤ 8388608 ∧ c.endB < c.residue

instance (c : Certificate) : Decidable (Accepted c) := by
  unfold Accepted
  infer_instance

def residues (cs : List Certificate) : List ℕ := cs.map Certificate.residue

theorem descent_of_accepted {c : Certificate} (h : Accepted c) (k : ℕ) :
    syracuseStep^[13] (8388608 * k + c.residue) < 8388608 * k + c.residue := by
  rcases h with ⟨hvalid, hlength, ha, hb⟩
  simpa only [hlength] using AffineTrace.strict_descent hvalid ha hb k

theorem descent_of_residue {c : Certificate} (h : Accepted c)
    (n : ℕ) (hn : n % 8388608 = c.residue) : syracuseStep^[13] n < n := by
  have hform : n = 8388608 * (n / 8388608) + c.residue := by omega
  rw [hform]
  exact descent_of_accepted h (n / 8388608)

/-- The proof consumes finite, kernel-checked certificate acceptance, not search output. -/
theorem descent_of_mem (cs : List Certificate) (hchecked : ∀ c ∈ cs, Accepted c)
    (n : ℕ) (h : n % 8388608 ∈ residues cs) : syracuseStep^[13] n < n := by
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

private def cs01 : List Certificate :=
[  certificateFrom 327 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5],
  certificateFrom 20647 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 1, 4],
  certificateFrom 24935 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3],
  certificateFrom 30023 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4],
  certificateFrom 32359 [1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4],
  certificateFrom 33127 [1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3],
  certificateFrom 43687 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3],
  certificateFrom 51111 [1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4],
  certificateFrom 51879 [1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 3, 3],
  certificateFrom 51943 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5],
  certificateFrom 58215 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6],
  certificateFrom 71847 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 4, 3],
  certificateFrom 73063 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5],
  certificateFrom 75367 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3],
  certificateFrom 90599 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3],
  certificateFrom 93351 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4],
  certificateFrom 95335 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5],
  certificateFrom 101543 [1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 2, 4],
  certificateFrom 102727 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4],
  certificateFrom 103527 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3],
  certificateFrom 110919 [1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4],
  certificateFrom 116839 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6],
  certificateFrom 117575 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5],
  certificateFrom 125031 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4],
  certificateFrom 132839 [1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5],
  certificateFrom 145735 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3],
  certificateFrom 149671 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 2, 6],
  certificateFrom 152743 [1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3],
  certificateFrom 160999 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5],
  certificateFrom 167271 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4],
  certificateFrom 168007 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 2, 5],
  certificateFrom 168423 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6],
  certificateFrom 169575 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4],
  certificateFrom 173927 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5],
  certificateFrom 177767 [1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4],
  certificateFrom 198471 [1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5],
  certificateFrom 205895 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 3, 4],
  certificateFrom 207079 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4],
  certificateFrom 212583 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5],
  certificateFrom 215271 [1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4],
  certificateFrom 220775 [1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5],
  certificateFrom 226663 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3],
  certificateFrom 228967 [1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3],
  certificateFrom 231335 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5],
  certificateFrom 239527 [1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5],
  certificateFrom 247719 [1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3],
  certificateFrom 254823 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3],
  certificateFrom 262215 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 6],
  certificateFrom 263399 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4],
  certificateFrom 268135 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6]]

private theorem checked01 : ∀ c ∈ cs01, Accepted c := by
  decide +kernel

private def cs02 : List Certificate :=
[  certificateFrom 271591 [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4],
  certificateFrom 276327 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4],
  certificateFrom 278631 [1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4],
  certificateFrom 286887 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 3, 6],
  certificateFrom 289959 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2, 3],
  certificateFrom 291559 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4],
  certificateFrom 295079 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 2, 4],
  certificateFrom 298151 [1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 2, 3],
  certificateFrom 299335 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3],
  certificateFrom 307527 [1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3],
  certificateFrom 309927 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 5],
  certificateFrom 311143 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7],
  certificateFrom 313447 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3],
  certificateFrom 320871 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4],
  certificateFrom 321639 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3],
  certificateFrom 322791 [1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3],
  certificateFrom 326759 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4],
  certificateFrom 329063 [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4],
  certificateFrom 334951 [1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4],
  certificateFrom 346279 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 5, 3],
  certificateFrom 347815 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 3, 4],
  certificateFrom 354471 [1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 3, 3],
  certificateFrom 357191 [1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4],
  certificateFrom 365031 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3],
  certificateFrom 372455 [1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4],
  certificateFrom 373223 [1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3],
  certificateFrom 385383 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6],
  certificateFrom 392039 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5],
  certificateFrom 404135 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 1, 6],
  certificateFrom 415463 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3],
  certificateFrom 420167 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5],
  certificateFrom 420583 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6],
  certificateFrom 435815 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6],
  certificateFrom 436583 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3],
  certificateFrom 448679 [1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 1, 4],
  certificateFrom 458823 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4, 3],
  certificateFrom 460007 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3],
  certificateFrom 464743 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3],
  certificateFrom 467431 [1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4],
  certificateFrom 468199 [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3],
  certificateFrom 470951 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 2, 4],
  certificateFrom 472935 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3],
  certificateFrom 475303 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 3, 5],
  certificateFrom 479143 [1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 2, 4],
  certificateFrom 480359 [1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4],
  certificateFrom 483495 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 6, 3],
  certificateFrom 486247 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4],
  certificateFrom 491687 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 2, 3],
  certificateFrom 501063 [1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5],
  certificateFrom 509671 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4]]

private theorem checked02 : ∀ c ∈ cs02, Accepted c := by
  decide +kernel

private def cs03 : List Certificate :=
[  certificateFrom 510439 [1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5],
  certificateFrom 515175 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5],
  certificateFrom 517863 [1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4],
  certificateFrom 529223 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5],
  certificateFrom 531559 [1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3],
  certificateFrom 536647 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 2, 6],
  certificateFrom 537447 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3],
  certificateFrom 552679 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5],
  certificateFrom 560871 [1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5],
  certificateFrom 565991 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4],
  certificateFrom 569063 [1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3],
  certificateFrom 574183 [1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4],
  certificateFrom 575303 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4],
  certificateFrom 581991 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3],
  certificateFrom 583495 [1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4],
  certificateFrom 587111 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6],
  certificateFrom 591335 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3],
  certificateFrom 599527 [1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3],
  certificateFrom 600743 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 4, 3],
  certificateFrom 601191 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6],
  certificateFrom 617191 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3],
  certificateFrom 624231 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5],
  certificateFrom 625383 [1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3],
  certificateFrom 631623 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4],
  certificateFrom 632423 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3],
  certificateFrom 639815 [1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4],
  certificateFrom 650407 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 3, 4],
  certificateFrom 652391 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5],
  certificateFrom 659783 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4],
  certificateFrom 666471 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5],
  certificateFrom 667559 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 2, 3],
  certificateFrom 674663 [1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5],
  certificateFrom 675751 [1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 3],
  certificateFrom 678567 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 2, 6],
  certificateFrom 682087 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4],
  certificateFrom 682855 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3],
  certificateFrom 691015 [1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3],
  certificateFrom 703207 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4],
  certificateFrom 711399 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4],
  certificateFrom 730983 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7],
  certificateFrom 733255 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 5, 3],
  certificateFrom 740679 [1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4],
  certificateFrom 741447 [1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3, 3],
  certificateFrom 754407 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5],
  certificateFrom 754791 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4],
  certificateFrom 762983 [1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4],
  certificateFrom 769639 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5],
  certificateFrom 770791 [1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3],
  certificateFrom 775527 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5],
  certificateFrom 775911 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6]]

private theorem checked03 : ∀ c ∈ cs03, Accepted c := by
  decide +kernel

private def cs04 : List Certificate :=
[  certificateFrom 783687 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3],
  certificateFrom 783719 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3],
  certificateFrom 788391 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5],
  certificateFrom 788807 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6],
  certificateFrom 797031 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6],
  certificateFrom 797799 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3],
  certificateFrom 803687 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5],
  certificateFrom 805223 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4],
  certificateFrom 820455 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4],
  certificateFrom 828231 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3],
  certificateFrom 833383 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4],
  certificateFrom 835655 [1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 1, 4],
  certificateFrom 836423 [1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3],
  certificateFrom 850535 [1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5],
  certificateFrom 852135 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 3, 4],
  certificateFrom 875175 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 5, 3],
  certificateFrom 876391 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5],
  certificateFrom 877895 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4],
  certificateFrom 878663 [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 1, 5],
  certificateFrom 882599 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4],
  certificateFrom 883367 [1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 3, 3],
  certificateFrom 886087 [1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4],
  certificateFrom 887271 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4],
  certificateFrom 895463 [1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4],
  certificateFrom 897895 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6],
  certificateFrom 906087 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4],
  certificateFrom 920903 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5],
  certificateFrom 924839 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 4, 4],
  certificateFrom 929095 [1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5],
  certificateFrom 933031 [1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4],
  certificateFrom 934215 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4],
  certificateFrom 937287 [1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3],
  certificateFrom 942407 [1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4],
  certificateFrom 951399 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3],
  certificateFrom 951783 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6],
  certificateFrom 958823 [1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4],
  certificateFrom 959559 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 3, 3],
  certificateFrom 959591 [1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3],
  certificateFrom 964327 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5],
  certificateFrom 965479 [1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3],
  certificateFrom 967751 [1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 3, 3],
  certificateFrom 972519 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3],
  certificateFrom 977575 [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 4],
  certificateFrom 985415 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3],
  certificateFrom 993607 [1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3],
  certificateFrom 993639 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3],
  certificateFrom 1001831 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3],
  certificateFrom 1006951 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4],
  certificateFrom 1009255 [1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4],
  certificateFrom 1015143 [1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4]]

private theorem checked04 : ∀ c ∈ cs04, Accepted c := by
  decide +kernel

private def cs05 : List Certificate :=
[  certificateFrom 1020583 [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 1, 5],
  certificateFrom 1028007 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 3, 4],
  certificateFrom 1032359 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 1, 7],
  certificateFrom 1043303 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4],
  certificateFrom 1045223 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3],
  certificateFrom 1051495 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4],
  certificateFrom 1053415 [1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3],
  certificateFrom 1062823 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5],
  certificateFrom 1071015 [1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5],
  certificateFrom 1071431 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4],
  certificateFrom 1072231 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5],
  certificateFrom 1079207 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3],
  certificateFrom 1079623 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4],
  certificateFrom 1094503 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3],
  certificateFrom 1094887 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4],
  certificateFrom 1101479 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 3, 3],
  certificateFrom 1102695 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3],
  certificateFrom 1103079 [1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4],
  certificateFrom 1108903 [1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 2, 4],
  certificateFrom 1109671 [1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 3, 3],
  certificateFrom 1109735 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5],
  certificateFrom 1113255 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 5],
  certificateFrom 1122631 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5],
  certificateFrom 1129639 [1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 2, 3],
  certificateFrom 1134759 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 2, 4],
  certificateFrom 1139015 [1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3],
  certificateFrom 1144135 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6],
  certificateFrom 1148391 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3],
  certificateFrom 1153127 [1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5],
  certificateFrom 1160551 [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4],
  certificateFrom 1181287 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5],
  certificateFrom 1188679 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4],
  certificateFrom 1195367 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5],
  certificateFrom 1211751 [1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3],
  certificateFrom 1223527 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7],
  certificateFrom 1227367 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4],
  certificateFrom 1235559 [1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4],
  certificateFrom 1255495 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 1, 4],
  certificateFrom 1263687 [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 4],
  certificateFrom 1280167 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 1, 4],
  certificateFrom 1281383 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6],
  certificateFrom 1283303 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5],
  certificateFrom 1283687 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4],
  certificateFrom 1289127 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 1, 5],
  certificateFrom 1291879 [1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4],
  certificateFrom 1296231 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5],
  certificateFrom 1297319 [1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 1, 5],
  certificateFrom 1298919 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4],
  certificateFrom 1299687 [1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3],
  certificateFrom 1305511 [1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 2, 3]]

private theorem checked05 : ∀ c ∈ cs05, Accepted c := by
  decide +kernel

private def cs06 : List Certificate :=
[  certificateFrom 1311463 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5],
  certificateFrom 1311847 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4],
  certificateFrom 1314983 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 3, 5],
  certificateFrom 1320007 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 1, 6],
  certificateFrom 1321191 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4],
  certificateFrom 1323175 [1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 1, 5],
  certificateFrom 1329383 [1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4],
  certificateFrom 1331367 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 2, 3],
  certificateFrom 1332551 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5],
  certificateFrom 1332583 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5],
  certificateFrom 1340743 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3],
  certificateFrom 1343079 [1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3],
  certificateFrom 1349351 [1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4],
  certificateFrom 1360743 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7],
  certificateFrom 1361831 [1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3],
  certificateFrom 1362279 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4],
  certificateFrom 1392743 [1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4],
  certificateFrom 1397415 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 1, 4],
  certificateFrom 1404071 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 3, 3],
  certificateFrom 1405607 [1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 4],
  certificateFrom 1405671 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6],
  certificateFrom 1412263 [1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 3, 3],
  certificateFrom 1413447 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3],
  certificateFrom 1421639 [1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3],
  certificateFrom 1433447 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5],
  certificateFrom 1434983 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4],
  certificateFrom 1435751 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3],
  certificateFrom 1439655 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4],
  certificateFrom 1440871 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6],
  certificateFrom 1443175 [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4],
  certificateFrom 1447847 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4],
  certificateFrom 1461927 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 1, 6],
  certificateFrom 1463111 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4],
  certificateFrom 1463143 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4],
  certificateFrom 1471303 [1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4],
  certificateFrom 1477959 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5],
  certificateFrom 1477991 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3],
  certificateFrom 1480295 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3],
  certificateFrom 1488487 [1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3],
  certificateFrom 1516615 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 4, 3],
  certificateFrom 1517799 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3],
  certificateFrom 1521383 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5],
  certificateFrom 1525223 [1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4],
  certificateFrom 1525991 [1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3],
  certificateFrom 1527655 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4],
  certificateFrom 1529959 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4],
  certificateFrom 1538151 [1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4],
  certificateFrom 1551079 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4],
  certificateFrom 1562791 [1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 2, 4],
  certificateFrom 1572967 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5]]

private theorem checked06 : ∀ c ∈ cs06, Accepted c := by
  decide +kernel

private def cs07 : List Certificate :=
[  certificateFrom 1574119 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3],
  certificateFrom 1581159 [1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5],
  certificateFrom 1581543 [1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4],
  certificateFrom 1582311 [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3],
  certificateFrom 1586279 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4],
  certificateFrom 1587047 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3],
  certificateFrom 1589351 [1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3],
  certificateFrom 1594471 [1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4],
  certificateFrom 1602279 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3],
  certificateFrom 1605799 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 3, 3],
  certificateFrom 1619879 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7],
  certificateFrom 1623783 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4],
  certificateFrom 1631591 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3],
  certificateFrom 1631975 [1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4],
  certificateFrom 1637479 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3],
  certificateFrom 1639783 [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3],
  certificateFrom 1645671 [1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3],
  certificateFrom 1651527 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5],
  certificateFrom 1658535 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 4, 3],
  certificateFrom 1667143 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 1, 4],
  certificateFrom 1667911 [1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3],
  certificateFrom 1670311 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 5],
  certificateFrom 1679687 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5],
  certificateFrom 1680103 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6],
  certificateFrom 1683175 [1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3],
  certificateFrom 1689415 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4],
  certificateFrom 1691815 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 3, 4],
  certificateFrom 1697607 [1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4],
  certificateFrom 1700007 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 1, 4],
  certificateFrom 1717575 [1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4],
  certificateFrom 1723495 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4],
  certificateFrom 1731687 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4],
  certificateFrom 1743015 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 1, 5],
  certificateFrom 1751207 [1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 1, 5],
  certificateFrom 1752423 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5],
  certificateFrom 1759399 [1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2, 3],
  certificateFrom 1761767 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5],
  certificateFrom 1764519 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 1, 6],
  certificateFrom 1769959 [1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5],
  certificateFrom 1773895 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6],
  certificateFrom 1774695 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5],
  certificateFrom 1778151 [1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3],
  certificateFrom 1781671 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 3, 3],
  certificateFrom 1789863 [1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 3, 3],
  certificateFrom 1791079 [1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3],
  certificateFrom 1796199 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6],
  certificateFrom 1796967 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3],
  certificateFrom 1802087 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8],
  certificateFrom 1809063 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 1, 4],
  certificateFrom 1817319 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6]]

private theorem checked07 : ∀ c ∈ cs07, Accepted c := by
  decide +kernel

private def cs08 : List Certificate :=
[  certificateFrom 1820391 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3],
  certificateFrom 1825511 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4],
  certificateFrom 1828583 [1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3],
  certificateFrom 1833319 [1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5],
  certificateFrom 1840359 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5],
  certificateFrom 1840743 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4],
  certificateFrom 1846183 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 2, 5],
  certificateFrom 1853287 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5],
  certificateFrom 1872039 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 1, 7],
  certificateFrom 1876711 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3],
  certificateFrom 1878247 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4],
  certificateFrom 1884903 [1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3],
  certificateFrom 1886023 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3],
  certificateFrom 1889607 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5],
  certificateFrom 1893447 [1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 1, 4],
  certificateFrom 1894215 [1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3],
  certificateFrom 1919303 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4],
  certificateFrom 1925991 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5],
  certificateFrom 1934567 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6],
  certificateFrom 1942343 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3],
  certificateFrom 1947495 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6],
  certificateFrom 1949767 [1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 4],
  certificateFrom 1950535 [1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3],
  certificateFrom 1961127 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 4, 3],
  certificateFrom 1966247 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 1, 6],
  certificateFrom 1970503 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3],
  certificateFrom 1979111 [1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4],
  certificateFrom 1984615 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5],
  certificateFrom 1992007 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4],
  certificateFrom 1992039 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4],
  certificateFrom 1992807 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3],
  certificateFrom 2000199 [1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4],
  certificateFrom 2001383 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4],
  certificateFrom 2005735 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5],
  certificateFrom 2009575 [1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4],
  certificateFrom 2013927 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3],
  certificateFrom 2022119 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3],
  certificateFrom 2035367 [1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 1, 4],
  certificateFrom 2038951 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 6],
  certificateFrom 2048327 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6],
  certificateFrom 2051399 [1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3],
  certificateFrom 2065511 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3],
  certificateFrom 2072935 [1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4],
  certificateFrom 2073703 [1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3],
  certificateFrom 2091687 [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 4],
  certificateFrom 2115175 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4],
  certificateFrom 2115943 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3],
  certificateFrom 2121063 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6],
  certificateFrom 2123367 [1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4],
  certificateFrom 2129991 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 5]]

private theorem checked08 : ∀ c ∈ cs08, Accepted c := by
  decide +kernel

private def cs09 : List Certificate :=
[  certificateFrom 2130023 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5],
  certificateFrom 2131175 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3],
  certificateFrom 2135911 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5],
  certificateFrom 2138183 [1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 1, 5],
  certificateFrom 2142119 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 1, 6],
  certificateFrom 2144103 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3],
  certificateFrom 2146375 [1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 3],
  certificateFrom 2157415 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6],
  certificateFrom 2162855 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 4, 3],
  certificateFrom 2165607 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4],
  certificateFrom 2180839 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4],
  certificateFrom 2185543 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6],
  certificateFrom 2188615 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3],
  certificateFrom 2193319 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3],
  certificateFrom 2193735 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4],
  certificateFrom 2196807 [1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3],
  certificateFrom 2197991 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3],
  certificateFrom 2206183 [1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3],
  certificateFrom 2208583 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5],
  certificateFrom 2208999 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6],
  certificateFrom 2210151 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4],
  certificateFrom 2216807 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3],
  certificateFrom 2218343 [1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4],
  certificateFrom 2221927 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8],
  certificateFrom 2235559 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 5, 3],
  certificateFrom 2243751 [1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 3, 3],
  certificateFrom 2244935 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3],
  certificateFrom 2246471 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4],
  certificateFrom 2253127 [1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3],
  certificateFrom 2253159 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5],
  certificateFrom 2261351 [1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5],
  certificateFrom 2266471 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4],
  certificateFrom 2269543 [1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3],
  certificateFrom 2271911 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 5],
  certificateFrom 2274663 [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4],
  certificateFrom 2280103 [1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 1, 5],
  certificateFrom 2288295 [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 3],
  certificateFrom 2300071 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 2, 5],
  certificateFrom 2302791 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6],
  certificateFrom 2303591 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5],
  certificateFrom 2317671 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3],
  certificateFrom 2318823 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5],
  certificateFrom 2319975 [1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3],
  certificateFrom 2325863 [1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3],
  certificateFrom 2331751 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5],
  certificateFrom 2337959 [1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 1, 4],
  certificateFrom 2338727 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 4, 3],
  certificateFrom 2341479 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4],
  certificateFrom 2347335 [1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4],
  certificateFrom 2349671 [1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4]]

private theorem checked09 : ∀ c ∈ cs09, Accepted c := by
  decide +kernel

private def cs10 : List Certificate :=
[  certificateFrom 2354023 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3],
  certificateFrom 2362215 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3],
  certificateFrom 2367335 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4],
  certificateFrom 2369607 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 2, 4],
  certificateFrom 2369639 [1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4],
  certificateFrom 2373959 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5],
  certificateFrom 2377799 [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 2, 4],
  certificateFrom 2380967 [1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 1, 5],
  certificateFrom 2382151 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3],
  certificateFrom 2382567 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4],
  certificateFrom 2390343 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3],
  certificateFrom 2394279 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 2, 4],
  certificateFrom 2403687 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4],
  certificateFrom 2405607 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3],
  certificateFrom 2411879 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4],
  certificateFrom 2413031 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4],
  certificateFrom 2413799 [1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3],
  certificateFrom 2419623 [1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 3, 3],
  certificateFrom 2425959 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6],
  certificateFrom 2445479 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 3, 3],
  certificateFrom 2454887 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5],
  certificateFrom 2455271 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4],
  certificateFrom 2463463 [1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4],
  certificateFrom 2471271 [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3],
  certificateFrom 2476391 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6],
  certificateFrom 2483047 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5],
  certificateFrom 2499399 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3],
  certificateFrom 2508007 [1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4],
  certificateFrom 2511527 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 2, 4],
  certificateFrom 2519719 [1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 2, 4],
  certificateFrom 2520935 [1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4],
  certificateFrom 2538087 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3],
  certificateFrom 2541671 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5],
  certificateFrom 2546279 [1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3],
  certificateFrom 2549063 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4],
  certificateFrom 2551015 [1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5],
  certificateFrom 2553767 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6],
  certificateFrom 2558439 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4],
  certificateFrom 2561959 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4],
  certificateFrom 2562791 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7],
  certificateFrom 2566215 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 2, 3],
  certificateFrom 2571367 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4],
  certificateFrom 2574407 [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 3],
  certificateFrom 2574503 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 3, 5],
  certificateFrom 2577223 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6],
  certificateFrom 2577255 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6],
  certificateFrom 2582695 [1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 1, 5],
  certificateFrom 2590887 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 2, 3],
  certificateFrom 2593255 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5],
  certificateFrom 2594407 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3]]

private theorem checked10 : ∀ c ∈ cs10, Accepted c := by
  decide +kernel

private def cs11 : List Certificate :=
[  certificateFrom 2601447 [1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5],
  certificateFrom 2602599 [1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3],
  certificateFrom 2609639 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3],
  certificateFrom 2622567 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3],
  certificateFrom 2631911 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3],
  certificateFrom 2639335 [1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4],
  certificateFrom 2640103 [1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3],
  certificateFrom 2641767 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6],
  certificateFrom 2643687 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5],
  certificateFrom 2644071 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4],
  certificateFrom 2652263 [1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4],
  certificateFrom 2660071 [1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3],
  certificateFrom 2664807 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5],
  certificateFrom 2665191 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4],
  certificateFrom 2672999 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3],
  certificateFrom 2687047 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 5],
  certificateFrom 2692967 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5],
  certificateFrom 2700391 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6],
  certificateFrom 2703463 [1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3],
  certificateFrom 2708135 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 2, 3],
  certificateFrom 2711719 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 4, 5],
  certificateFrom 2715559 [1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 4],
  certificateFrom 2716327 [1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 3],
  certificateFrom 2722663 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4],
  certificateFrom 2745703 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3],
  certificateFrom 2750375 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3],
  certificateFrom 2750791 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4],
  certificateFrom 2753895 [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3],
  certificateFrom 2757799 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 1, 4],
  certificateFrom 2758567 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3],
  certificateFrom 2765671 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5],
  certificateFrom 2765991 [1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 1, 4],
  certificateFrom 2773831 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3],
  certificateFrom 2773863 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3],
  certificateFrom 2781255 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 2, 4],
  certificateFrom 2782023 [1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3],
  certificateFrom 2787175 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4],
  certificateFrom 2805927 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 1, 6],
  certificateFrom 2810215 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5],
  certificateFrom 2810599 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4],
  certificateFrom 2814119 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 2, 4],
  certificateFrom 2819559 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5],
  certificateFrom 2823495 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4],
  certificateFrom 2827751 [1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5],
  certificateFrom 2828967 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 2, 5],
  certificateFrom 2831687 [1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4],
  certificateFrom 2835943 [1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3],
  certificateFrom 2837607 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6],
  certificateFrom 2838375 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3],
  certificateFrom 2840679 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3]]

private theorem checked11 : ∀ c ∈ cs11, Accepted c := by
  decide +kernel

private def cs12 : List Certificate :=
[  certificateFrom 2845415 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5],
  certificateFrom 2845799 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4],
  certificateFrom 2848871 [1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3],
  certificateFrom 2851687 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8],
  certificateFrom 2853607 [1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5],
  certificateFrom 2860647 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5],
  certificateFrom 2861799 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3],
  certificateFrom 2873511 [1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 3, 3],
  certificateFrom 2876231 [1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4],
  certificateFrom 2892263 [1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3],
  certificateFrom 2896999 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3],
  certificateFrom 2898535 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4],
  certificateFrom 2905191 [1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3],
  certificateFrom 2919239 [1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5],
  certificateFrom 2923175 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 2, 4],
  certificateFrom 2926663 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 3, 4],
  certificateFrom 2927847 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4],
  certificateFrom 2931015 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7],
  certificateFrom 2934503 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3],
  certificateFrom 2936039 [1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4],
  certificateFrom 2942695 [1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3],
  certificateFrom 2951335 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 3, 4],
  certificateFrom 2954855 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6],
  certificateFrom 2959527 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 1, 4],
  certificateFrom 2961479 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 3, 5],
  certificateFrom 2969671 [1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 1, 5],
  certificateFrom 2970087 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4],
  certificateFrom 2977863 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 2, 3],
  certificateFrom 2978279 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4],
  certificateFrom 2992359 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6],
  certificateFrom 2999399 [1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4],
  certificateFrom 3000135 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3],
  certificateFrom 3002535 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 4, 3],
  certificateFrom 3007559 [1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 2, 4],
  certificateFrom 3008327 [1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3],
  certificateFrom 3010727 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 2, 3],
  certificateFrom 3011911 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5],
  certificateFrom 3011943 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5],
  certificateFrom 3026023 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5],
  certificateFrom 3028295 [1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3],
  certificateFrom 3033415 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4],
  certificateFrom 3034215 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3],
  certificateFrom 3042407 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3],
  certificateFrom 3049831 [1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4],
  certificateFrom 3068583 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 3, 4],
  certificateFrom 3093223 [1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4],
  certificateFrom 3103399 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 3, 5],
  certificateFrom 3106151 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6],
  certificateFrom 3111591 [1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 1, 5],
  certificateFrom 3119015 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4]]

private theorem checked12 : ∀ c ∈ cs12, Accepted c := by
  decide +kernel

private def cs13 : List Certificate :=
[  certificateFrom 3119783 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 2, 3],
  certificateFrom 3131559 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 7],
  certificateFrom 3136231 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3],
  certificateFrom 3149479 [1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 2, 4],
  certificateFrom 3150311 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7],
  certificateFrom 3150695 [1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4],
  certificateFrom 3151463 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3],
  certificateFrom 3169447 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 1, 4],
  certificateFrom 3178823 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4],
  certificateFrom 3187783 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 1, 5],
  certificateFrom 3188967 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3],
  certificateFrom 3193703 [1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5],
  certificateFrom 3195975 [1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 1, 5],
  certificateFrom 3200743 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5],
  certificateFrom 3201127 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4],
  certificateFrom 3204167 [1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 2, 3],
  certificateFrom 3213639 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5],
  certificateFrom 3221831 [1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5],
  certificateFrom 3221863 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5],
  certificateFrom 3222247 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4],
  certificateFrom 3229287 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6],
  certificateFrom 3230023 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3],
  certificateFrom 3230439 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4],
  certificateFrom 3251559 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4],
  certificateFrom 3260487 [1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 3],
  certificateFrom 3268775 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 2, 7],
  certificateFrom 3273447 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5],
  certificateFrom 3281639 [1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5],
  certificateFrom 3289831 [1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3],
  certificateFrom 3294951 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6],
  certificateFrom 3296071 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4],
  certificateFrom 3302727 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3],
  certificateFrom 3302759 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3],
  certificateFrom 3304263 [1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4],
  certificateFrom 3310919 [1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3],
  certificateFrom 3312103 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3],
  certificateFrom 3320295 [1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3],
  certificateFrom 3322727 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5],
  certificateFrom 3324263 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4],
  certificateFrom 3329703 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 1, 5],
  certificateFrom 3332455 [1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4],
  certificateFrom 3337895 [1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 1, 5],
  certificateFrom 3338311 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 3, 4],
  certificateFrom 3339495 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4],
  certificateFrom 3346087 [1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 2, 3],
  certificateFrom 3346503 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 1, 4],
  certificateFrom 3360583 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6],
  certificateFrom 3371175 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 3, 4],
  certificateFrom 3376615 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5],
  certificateFrom 3380583 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6]]

private theorem checked13 : ∀ c ∈ cs13, Accepted c := by
  decide +kernel

private def cs14 : List Certificate :=
[  certificateFrom 3383655 [1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3],
  certificateFrom 3402407 [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 3, 3],
  certificateFrom 3402471 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7],
  certificateFrom 3402855 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4],
  certificateFrom 3416935 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4],
  certificateFrom 3425895 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3],
  certificateFrom 3434087 [1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3],
  certificateFrom 3452071 [1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 2, 4],
  certificateFrom 3461447 [1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4],
  certificateFrom 3475559 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4],
  certificateFrom 3476327 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3],
  certificateFrom 3480231 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 3, 4],
  certificateFrom 3481447 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6],
  certificateFrom 3483751 [1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4],
  certificateFrom 3488423 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 1, 4],
  certificateFrom 3491559 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3],
  certificateFrom 3496679 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6],
  certificateFrom 3504455 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3],
  certificateFrom 3517799 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6],
  certificateFrom 3518535 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 1, 7],
  certificateFrom 3520871 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3],
  certificateFrom 3525991 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4],
  certificateFrom 3528295 [1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4],
  certificateFrom 3529063 [1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3],
  certificateFrom 3557191 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3],
  certificateFrom 3565799 [1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4],
  certificateFrom 3568967 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5],
  certificateFrom 3569383 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6],
  certificateFrom 3570535 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4],
  certificateFrom 3571303 [1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5],
  certificateFrom 3577191 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3],
  certificateFrom 3578727 [1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4],
  certificateFrom 3583079 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7],
  certificateFrom 3585383 [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3],
  certificateFrom 3590055 [1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5],
  certificateFrom 3590471 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4],
  certificateFrom 3598663 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4],
  certificateFrom 3622119 [1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4],
  certificateFrom 3626855 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4],
  certificateFrom 3632295 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 1, 5],
  certificateFrom 3635047 [1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4],
  certificateFrom 3640487 [1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 1, 5],
  certificateFrom 3641671 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5],
  certificateFrom 3648679 [1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2, 3],
  certificateFrom 3649863 [1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5],
  certificateFrom 3652199 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3],
  certificateFrom 3658055 [1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3],
  certificateFrom 3660391 [1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3],
  certificateFrom 3660455 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 1, 7],
  certificateFrom 3663175 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6]]

private theorem checked14 : ∀ c ∈ cs14, Accepted c := by
  decide +kernel

private def cs15 : List Certificate :=
[  certificateFrom 3663975 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5],
  certificateFrom 3672551 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6],
  certificateFrom 3678055 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3],
  certificateFrom 3679591 [1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4],
  certificateFrom 3680327 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 3, 3],
  certificateFrom 3680359 [1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3],
  certificateFrom 3685479 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4],
  certificateFrom 3688519 [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 3, 3],
  certificateFrom 3693287 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3],
  certificateFrom 3704999 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 3, 3],
  certificateFrom 3706215 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5],
  certificateFrom 3707719 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4],
  certificateFrom 3714407 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3],
  certificateFrom 3722599 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3],
  certificateFrom 3723751 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3],
  certificateFrom 3744839 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 2, 5],
  certificateFrom 3765991 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3],
  certificateFrom 3770695 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7],
  certificateFrom 3774183 [1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3],
  certificateFrom 3802343 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5],
  certificateFrom 3810535 [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5],
  certificateFrom 3815271 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5],
  certificateFrom 3818727 [1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3],
  certificateFrom 3822247 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 3, 3],
  certificateFrom 3829671 [1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 4],
  certificateFrom 3830439 [1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 3, 3],
  certificateFrom 3830503 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5],
  certificateFrom 3830887 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4],
  certificateFrom 3831655 [1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3],
  certificateFrom 3834023 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 1, 5],
  certificateFrom 3836775 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6],
  certificateFrom 3859783 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3],
  certificateFrom 3864903 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6],
  certificateFrom 3865703 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5],
  certificateFrom 3868391 [1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4],
  certificateFrom 3869159 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3],
  certificateFrom 3871911 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 2, 4],
  certificateFrom 3872679 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3],
  certificateFrom 3873895 [1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5],
  certificateFrom 3880103 [1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 2, 4],
  certificateFrom 3881319 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4],
  certificateFrom 3882087 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3],
  certificateFrom 3886759 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 2, 5],
  certificateFrom 3901287 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6],
  certificateFrom 3911399 [1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5],
  certificateFrom 3924711 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4],
  certificateFrom 3934023 [1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4],
  certificateFrom 3937607 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6],
  certificateFrom 3948135 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4],
  certificateFrom 3950055 [1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3]]

private theorem checked15 : ∀ c ∈ cs15, Accepted c := by
  decide +kernel

private def cs16 : List Certificate :=
[  certificateFrom 3954791 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3],
  certificateFrom 3956327 [1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4],
  certificateFrom 3962983 [1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3],
  certificateFrom 3966887 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4],
  certificateFrom 3975079 [1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4],
  certificateFrom 3975911 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3],
  certificateFrom 3990343 [1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4],
  certificateFrom 4009895 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 1, 5],
  certificateFrom 4012647 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6],
  certificateFrom 4018087 [1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 1, 5],
  certificateFrom 4025191 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5],
  certificateFrom 4026279 [1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 3],
  certificateFrom 4033383 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3],
  certificateFrom 4040775 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 1, 6],
  certificateFrom 4041959 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4],
  certificateFrom 4050151 [1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4],
  certificateFrom 4061511 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3],
  certificateFrom 4065447 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 1, 6],
  certificateFrom 4068519 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2, 3],
  certificateFrom 4073639 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 2, 4],
  certificateFrom 4076711 [1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 2, 3],
  certificateFrom 4083047 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4],
  certificateFrom 4084199 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6],
  certificateFrom 4091975 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 3, 3],
  certificateFrom 4092391 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4],
  certificateFrom 4097895 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3],
  certificateFrom 4104935 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5],
  certificateFrom 4113127 [1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5],
  certificateFrom 4113511 [1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4],
  certificateFrom 4121319 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3],
  certificateFrom 4124839 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 3, 3],
  certificateFrom 4134215 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3],
  certificateFrom 4142407 [1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3],
  certificateFrom 4155751 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4],
  certificateFrom 4156519 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3]]

private theorem checked16 : ∀ c ∈ cs16, Accepted c := by
  decide +kernel

private theorem append_checked
    {xs ys : List Certificate}
    (hx : ∀ c ∈ xs, Accepted c) (hy : ∀ c ∈ ys, Accepted c) :
    ∀ c ∈ xs ++ ys, Accepted c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hx c hc
  · exact hy c hc

private def certificates : List Certificate :=
  cs01 ++ (cs02 ++ (cs03 ++ (cs04 ++ (cs05 ++ (cs06 ++ (cs07 ++ (cs08 ++ (cs09 ++ (cs10 ++ (cs11 ++ (cs12 ++ (cs13 ++ (cs14 ++ (cs15 ++ (cs16)))))))))))))))

private theorem certificates_checked : ∀ c ∈ certificates, Accepted c := by
  exact append_checked checked01 (append_checked checked02 (append_checked checked03 (append_checked checked04 (append_checked checked05 (append_checked checked06 (append_checked checked07 (append_checked checked08 (append_checked checked09 (append_checked checked10 (append_checked checked11 (append_checked checked12 (append_checked checked13 (append_checked checked14 (append_checked checked15 (checked16)))))))))))))))

private def rawResidues : List ℕ :=
[  327, 20647, 24935, 30023, 32359, 33127, 43687, 51111, 51879, 51943, 58215, 71847, 73063, 75367,
  90599, 93351, 95335, 101543, 102727, 103527, 110919, 116839, 117575, 125031, 132839, 145735, 149671, 152743,
  160999, 167271, 168007, 168423, 169575, 173927, 177767, 198471, 205895, 207079, 212583, 215271, 220775, 226663,
  228967, 231335, 239527, 247719, 254823, 262215, 263399, 268135, 271591, 276327, 278631, 286887, 289959, 291559,
  295079, 298151, 299335, 307527, 309927, 311143, 313447, 320871, 321639, 322791, 326759, 329063, 334951, 346279,
  347815, 354471, 357191, 365031, 372455, 373223, 385383, 392039, 404135, 415463, 420167, 420583, 435815, 436583,
  448679, 458823, 460007, 464743, 467431, 468199, 470951, 472935, 475303, 479143, 480359, 483495, 486247, 491687,
  501063, 509671, 510439, 515175, 517863, 529223, 531559, 536647, 537447, 552679, 560871, 565991, 569063, 574183,
  575303, 581991, 583495, 587111, 591335, 599527, 600743, 601191, 617191, 624231, 625383, 631623, 632423, 639815,
  650407, 652391, 659783, 666471, 667559, 674663, 675751, 678567, 682087, 682855, 691015, 703207, 711399, 730983,
  733255, 740679, 741447, 754407, 754791, 762983, 769639, 770791, 775527, 775911, 783687, 783719, 788391, 788807,
  797031, 797799, 803687, 805223, 820455, 828231, 833383, 835655, 836423, 850535, 852135, 875175, 876391, 877895,
  878663, 882599, 883367, 886087, 887271, 895463, 897895, 906087, 920903, 924839, 929095, 933031, 934215, 937287,
  942407, 951399, 951783, 958823, 959559, 959591, 964327, 965479, 967751, 972519, 977575, 985415, 993607, 993639,
  1001831, 1006951, 1009255, 1015143, 1020583, 1028007, 1032359, 1043303, 1045223, 1051495, 1053415, 1062823, 1071015, 1071431,
  1072231, 1079207, 1079623, 1094503, 1094887, 1101479, 1102695, 1103079, 1108903, 1109671, 1109735, 1113255, 1122631, 1129639,
  1134759, 1139015, 1144135, 1148391, 1153127, 1160551, 1181287, 1188679, 1195367, 1211751, 1223527, 1227367, 1235559, 1255495,
  1263687, 1280167, 1281383, 1283303, 1283687, 1289127, 1291879, 1296231, 1297319, 1298919, 1299687, 1305511, 1311463, 1311847,
  1314983, 1320007, 1321191, 1323175, 1329383, 1331367, 1332551, 1332583, 1340743, 1343079, 1349351, 1360743, 1361831, 1362279,
  1392743, 1397415, 1404071, 1405607, 1405671, 1412263, 1413447, 1421639, 1433447, 1434983, 1435751, 1439655, 1440871, 1443175,
  1447847, 1461927, 1463111, 1463143, 1471303, 1477959, 1477991, 1480295, 1488487, 1516615, 1517799, 1521383, 1525223, 1525991,
  1527655, 1529959, 1538151, 1551079, 1562791, 1572967, 1574119, 1581159, 1581543, 1582311, 1586279, 1587047, 1589351, 1594471,
  1602279, 1605799, 1619879, 1623783, 1631591, 1631975, 1637479, 1639783, 1645671, 1651527, 1658535, 1667143, 1667911, 1670311,
  1679687, 1680103, 1683175, 1689415, 1691815, 1697607, 1700007, 1717575, 1723495, 1731687, 1743015, 1751207, 1752423, 1759399,
  1761767, 1764519, 1769959, 1773895, 1774695, 1778151, 1781671, 1789863, 1791079, 1796199, 1796967, 1802087, 1809063, 1817319,
  1820391, 1825511, 1828583, 1833319, 1840359, 1840743, 1846183, 1853287, 1872039, 1876711, 1878247, 1884903, 1886023, 1889607,
  1893447, 1894215, 1919303, 1925991, 1934567, 1942343, 1947495, 1949767, 1950535, 1961127, 1966247, 1970503, 1979111, 1984615,
  1992007, 1992039, 1992807, 2000199, 2001383, 2005735, 2009575, 2013927, 2022119, 2035367, 2038951, 2048327, 2051399, 2065511,
  2072935, 2073703, 2091687, 2115175, 2115943, 2121063, 2123367, 2129991, 2130023, 2131175, 2135911, 2138183, 2142119, 2144103,
  2146375, 2157415, 2162855, 2165607, 2180839, 2185543, 2188615, 2193319, 2193735, 2196807, 2197991, 2206183, 2208583, 2208999,
  2210151, 2216807, 2218343, 2221927, 2235559, 2243751, 2244935, 2246471, 2253127, 2253159, 2261351, 2266471, 2269543, 2271911,
  2274663, 2280103, 2288295, 2300071, 2302791, 2303591, 2317671, 2318823, 2319975, 2325863, 2331751, 2337959, 2338727, 2341479,
  2347335, 2349671, 2354023, 2362215, 2367335, 2369607, 2369639, 2373959, 2377799, 2380967, 2382151, 2382567, 2390343, 2394279,
  2403687, 2405607, 2411879, 2413031, 2413799, 2419623, 2425959, 2445479, 2454887, 2455271, 2463463, 2471271, 2476391, 2483047,
  2499399, 2508007, 2511527, 2519719, 2520935, 2538087, 2541671, 2546279, 2549063, 2551015, 2553767, 2558439, 2561959, 2562791,
  2566215, 2571367, 2574407, 2574503, 2577223, 2577255, 2582695, 2590887, 2593255, 2594407, 2601447, 2602599, 2609639, 2622567,
  2631911, 2639335, 2640103, 2641767, 2643687, 2644071, 2652263, 2660071, 2664807, 2665191, 2672999, 2687047, 2692967, 2700391,
  2703463, 2708135, 2711719, 2715559, 2716327, 2722663, 2745703, 2750375, 2750791, 2753895, 2757799, 2758567, 2765671, 2765991,
  2773831, 2773863, 2781255, 2782023, 2787175, 2805927, 2810215, 2810599, 2814119, 2819559, 2823495, 2827751, 2828967, 2831687,
  2835943, 2837607, 2838375, 2840679, 2845415, 2845799, 2848871, 2851687, 2853607, 2860647, 2861799, 2873511, 2876231, 2892263,
  2896999, 2898535, 2905191, 2919239, 2923175, 2926663, 2927847, 2931015, 2934503, 2936039, 2942695, 2951335, 2954855, 2959527,
  2961479, 2969671, 2970087, 2977863, 2978279, 2992359, 2999399, 3000135, 3002535, 3007559, 3008327, 3010727, 3011911, 3011943,
  3026023, 3028295, 3033415, 3034215, 3042407, 3049831, 3068583, 3093223, 3103399, 3106151, 3111591, 3119015, 3119783, 3131559,
  3136231, 3149479, 3150311, 3150695, 3151463, 3169447, 3178823, 3187783, 3188967, 3193703, 3195975, 3200743, 3201127, 3204167,
  3213639, 3221831, 3221863, 3222247, 3229287, 3230023, 3230439, 3251559, 3260487, 3268775, 3273447, 3281639, 3289831, 3294951,
  3296071, 3302727, 3302759, 3304263, 3310919, 3312103, 3320295, 3322727, 3324263, 3329703, 3332455, 3337895, 3338311, 3339495,
  3346087, 3346503, 3360583, 3371175, 3376615, 3380583, 3383655, 3402407, 3402471, 3402855, 3416935, 3425895, 3434087, 3452071,
  3461447, 3475559, 3476327, 3480231, 3481447, 3483751, 3488423, 3491559, 3496679, 3504455, 3517799, 3518535, 3520871, 3525991,
  3528295, 3529063, 3557191, 3565799, 3568967, 3569383, 3570535, 3571303, 3577191, 3578727, 3583079, 3585383, 3590055, 3590471,
  3598663, 3622119, 3626855, 3632295, 3635047, 3640487, 3641671, 3648679, 3649863, 3652199, 3658055, 3660391, 3660455, 3663175,
  3663975, 3672551, 3678055, 3679591, 3680327, 3680359, 3685479, 3688519, 3693287, 3704999, 3706215, 3707719, 3714407, 3722599,
  3723751, 3744839, 3765991, 3770695, 3774183, 3802343, 3810535, 3815271, 3818727, 3822247, 3829671, 3830439, 3830503, 3830887,
  3831655, 3834023, 3836775, 3859783, 3864903, 3865703, 3868391, 3869159, 3871911, 3872679, 3873895, 3880103, 3881319, 3882087,
  3886759, 3901287, 3911399, 3924711, 3934023, 3937607, 3948135, 3950055, 3954791, 3956327, 3962983, 3966887, 3975079, 3975911,
  3990343, 4009895, 4012647, 4018087, 4025191, 4026279, 4033383, 4040775, 4041959, 4050151, 4061511, 4065447, 4068519, 4073639,
  4076711, 4083047, 4084199, 4091975, 4092391, 4097895, 4104935, 4113127, 4113511, 4121319, 4124839, 4134215, 4142407, 4155751,
  4156519]

private theorem certificateFrom_residue (r : ℕ) (es : List ℕ) :
    (certificateFrom r es).residue = r := by
  rfl

private theorem residue_map :
    certificates.map Certificate.residue = rawResidues := by
  simp only [certificates, cs01, cs02, cs03, cs04, cs05, cs06, cs07, cs08, cs09, cs10, cs11, cs12, cs13, cs14, cs15, cs16, rawResidues,
    List.map_append, List.map_cons, List.map_nil, certificateFrom_residue,
    List.cons_append, List.nil_append]

private theorem target_mem_iff (r : ℕ) :
    r ∈ syracuseSevenMod32New23Step13Chunk01Classes ↔ r ∈ rawResidues := by
  simp only [syracuseSevenMod32New23Step13Chunk01Classes, rawResidues,
    Finset.mem_insert, Finset.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]

end Session67Parents

theorem solution (n : ℕ)
    (h : n % 8388608 ∈ syracuseSevenMod32New23Step13Chunk01Classes) :
    syracuseStep^[13] n < n := by
  have hr : n % 8388608 ∈ Session67Parents.rawResidues :=
    (Session67Parents.target_mem_iff _).mp h
  have hc : n % 8388608 ∈
      Session67Parents.Batch.residues Session67Parents.certificates := by
    simpa only [Session67Parents.Batch.residues, Session67Parents.residue_map] using hr
  exact Session67Parents.Batch.descent_of_mem Session67Parents.certificates
    Session67Parents.certificates_checked n hc

#print axioms Session67Parents.certificates_checked
#print axioms solution
