-- Prove2me | solution 1 for syracuse_descent_new23_step13_chunk02_seven_mod32
-- status  : ACCEPTED   (prove)
-- author  : @FakeMink
-- created : 2026-10-03T00:06:01.079886+00:00
-- url     : https://prove2.me/submissions/476bbb97-cc86-4b17-a58b-bc42e678b108

import Definitions.Def_syracuseSevenMod32New23Step13Chunk02Classes
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
[  certificateFrom 4163943 [1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4],
  certificateFrom 4170567 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5],
  certificateFrom 4178759 [1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5],
  certificateFrom 4182695 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 1, 6],
  certificateFrom 4186951 [1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3],
  certificateFrom 4189351 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 2, 5],
  certificateFrom 4198727 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5],
  certificateFrom 4209255 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3],
  certificateFrom 4221031 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5],
  certificateFrom 4233127 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6],
  certificateFrom 4233895 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 3, 3],
  certificateFrom 4236615 [1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4],
  certificateFrom 4237383 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 4, 3],
  certificateFrom 4238567 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3],
  certificateFrom 4242151 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5],
  certificateFrom 4242535 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4],
  certificateFrom 4245991 [1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4],
  certificateFrom 4246759 [1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3],
  certificateFrom 4250727 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4],
  certificateFrom 4256615 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4],
  certificateFrom 4262055 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 4, 3],
  certificateFrom 4263271 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7],
  certificateFrom 4264807 [1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4],
  certificateFrom 4270247 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 2, 3],
  certificateFrom 4279623 [1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5],
  certificateFrom 4280807 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3],
  certificateFrom 4283559 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 2, 4],
  certificateFrom 4288231 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4],
  certificateFrom 4288999 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3],
  certificateFrom 4292935 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4],
  certificateFrom 4293735 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5],
  certificateFrom 4296423 [1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4],
  certificateFrom 4301927 [1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5],
  certificateFrom 4310119 [1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3],
  certificateFrom 4315239 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6],
  certificateFrom 4318279 [1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 3, 3],
  certificateFrom 4336359 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6],
  certificateFrom 4344135 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3],
  certificateFrom 4344167 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5],
  certificateFrom 4344551 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4],
  certificateFrom 4359399 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5],
  certificateFrom 4359783 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4],
  certificateFrom 4360551 [1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3],
  certificateFrom 4365671 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4],
  certificateFrom 4372327 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5],
  certificateFrom 4379303 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 4, 3],
  certificateFrom 4391079 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 2, 5],
  certificateFrom 4403943 [1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3],
  certificateFrom 4410183 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4],
  certificateFrom 4410215 [1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4]]

private theorem checked01 : ∀ c ∈ cs01, Accepted c := by
  decide +kernel

private def cs02 : List Certificate :=
[  certificateFrom 4418375 [1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4],
  certificateFrom 4421543 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5],
  certificateFrom 4422759 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7],
  certificateFrom 4428967 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 3, 4],
  certificateFrom 4429735 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3],
  certificateFrom 4445031 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5],
  certificateFrom 4452423 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 1, 6],
  certificateFrom 4453607 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4],
  certificateFrom 4460199 [1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 3, 3],
  certificateFrom 4460615 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 2, 4],
  certificateFrom 4461415 [1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3],
  certificateFrom 4463783 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 5],
  certificateFrom 4471975 [1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 1, 5],
  certificateFrom 4473159 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5],
  certificateFrom 4480167 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 2, 3],
  certificateFrom 4481351 [1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5],
  certificateFrom 4481767 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4],
  certificateFrom 4485287 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 1, 6],
  certificateFrom 4489543 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3],
  certificateFrom 4489959 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4],
  certificateFrom 4511079 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4],
  certificateFrom 4511847 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3],
  certificateFrom 4516967 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6],
  certificateFrom 4531047 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6],
  certificateFrom 4532967 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3],
  certificateFrom 4541159 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3],
  certificateFrom 4545895 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5],
  certificateFrom 4554087 [1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5],
  certificateFrom 4562279 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3],
  certificateFrom 4566951 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 2, 5],
  certificateFrom 4582247 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5],
  certificateFrom 4586087 [1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4],
  certificateFrom 4589671 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6],
  certificateFrom 4594343 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 1, 6],
  certificateFrom 4599015 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4],
  certificateFrom 4602535 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 2, 4],
  certificateFrom 4603751 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4],
  certificateFrom 4606791 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3],
  certificateFrom 4610375 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5],
  certificateFrom 4611943 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4],
  certificateFrom 4614215 [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 4],
  certificateFrom 4614983 [1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3],
  certificateFrom 4630695 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 3, 4],
  certificateFrom 4633831 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5],
  certificateFrom 4634983 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3],
  certificateFrom 4642023 [1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5],
  certificateFrom 4642407 [1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4],
  certificateFrom 4643175 [1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3],
  certificateFrom 4647847 [1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 1, 5],
  certificateFrom 4649031 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 4, 3]]

private theorem checked02 : ∀ c ∈ cs02, Accepted c := by
  decide +kernel

private def cs03 : List Certificate :=
[  certificateFrom 4649447 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4],
  certificateFrom 4650215 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3],
  certificateFrom 4656455 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4],
  certificateFrom 4657223 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 3],
  certificateFrom 4661991 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7],
  certificateFrom 4664647 [1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4],
  certificateFrom 4673703 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 1, 5],
  certificateFrom 4679911 [1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4],
  certificateFrom 4681895 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 4, 3],
  certificateFrom 4684647 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4],
  certificateFrom 4692839 [1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4],
  certificateFrom 4699879 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4],
  certificateFrom 4704583 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6],
  certificateFrom 4712775 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4],
  certificateFrom 4713575 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3],
  certificateFrom 4727623 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5],
  certificateFrom 4727655 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3],
  certificateFrom 4740967 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6],
  certificateFrom 4756135 [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 4],
  certificateFrom 4759719 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 8],
  certificateFrom 4762791 [1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 3, 3],
  certificateFrom 4772167 [1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3],
  certificateFrom 4786279 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3],
  certificateFrom 4790951 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3],
  certificateFrom 4793703 [1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4],
  certificateFrom 4794471 [1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3],
  certificateFrom 4799143 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 2, 3],
  certificateFrom 4799207 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7],
  certificateFrom 4806567 [1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4],
  certificateFrom 4821831 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4],
  certificateFrom 4822631 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5],
  certificateFrom 4830823 [1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5],
  certificateFrom 4836711 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3],
  certificateFrom 4839015 [1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3],
  certificateFrom 4840615 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 3, 4],
  certificateFrom 4848807 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 4],
  certificateFrom 4849991 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4],
  certificateFrom 4850791 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5],
  certificateFrom 4858183 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4],
  certificateFrom 4860135 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5],
  certificateFrom 4868327 [1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5],
  certificateFrom 4876519 [1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3],
  certificateFrom 4881255 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3],
  certificateFrom 4888679 [1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4],
  certificateFrom 4889447 [1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3],
  certificateFrom 4901191 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3],
  certificateFrom 4901223 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5],
  certificateFrom 4901607 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4],
  certificateFrom 4909383 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3],
  certificateFrom 4922727 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4]]

private theorem checked03 : ∀ c ∈ cs03, Accepted c := by
  decide +kernel

private def cs04 : List Certificate :=
[  certificateFrom 4930919 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4],
  certificateFrom 4931687 [1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5],
  certificateFrom 4932839 [1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3],
  certificateFrom 4937575 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3],
  certificateFrom 4944999 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4],
  certificateFrom 4945767 [1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3],
  certificateFrom 4967239 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4],
  certificateFrom 4973927 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5],
  certificateFrom 4978599 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5],
  certificateFrom 4982119 [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5],
  certificateFrom 4982503 [1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4],
  certificateFrom 4990311 [1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3],
  certificateFrom 4995431 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6],
  certificateFrom 4996199 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3],
  certificateFrom 5002055 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5],
  certificateFrom 5002087 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5],
  certificateFrom 5010247 [1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5],
  certificateFrom 5010663 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4],
  certificateFrom 5017671 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 3, 4],
  certificateFrom 5018439 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3],
  certificateFrom 5018855 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4],
  certificateFrom 5020839 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 7],
  certificateFrom 5023591 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4],
  certificateFrom 5024679 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 1, 4],
  certificateFrom 5030215 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7],
  certificateFrom 5031783 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4],
  certificateFrom 5032871 [1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 4],
  certificateFrom 5048135 [1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4],
  certificateFrom 5058727 [1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 1, 4],
  certificateFrom 5062247 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4],
  certificateFrom 5066599 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5],
  certificateFrom 5068103 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4],
  certificateFrom 5070439 [1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4],
  certificateFrom 5080999 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4],
  certificateFrom 5089191 [1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4],
  certificateFrom 5101735 [1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 1, 5],
  certificateFrom 5102951 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7],
  certificateFrom 5120487 [1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5],
  certificateFrom 5125223 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5],
  certificateFrom 5133415 [1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5],
  certificateFrom 5140391 [1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 3, 3],
  certificateFrom 5141607 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3],
  certificateFrom 5159591 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 3, 4],
  certificateFrom 5162727 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5],
  certificateFrom 5167431 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7],
  certificateFrom 5170919 [1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5],
  certificateFrom 5179111 [1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3],
  certificateFrom 5182631 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 3, 3],
  certificateFrom 5190823 [1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 3, 3],
  certificateFrom 5190887 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7]]

private theorem checked04 : ∀ c ∈ cs04, Accepted c := by
  decide +kernel

private def cs05 : List Certificate :=
[  certificateFrom 5192039 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3],
  certificateFrom 5197159 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6],
  certificateFrom 5228359 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5],
  certificateFrom 5230759 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 2, 5],
  certificateFrom 5235431 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3],
  certificateFrom 5236551 [1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5],
  certificateFrom 5241703 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4],
  certificateFrom 5244743 [1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3],
  certificateFrom 5258855 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3],
  certificateFrom 5262439 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5],
  certificateFrom 5267047 [1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3],
  certificateFrom 5269831 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4],
  certificateFrom 5269863 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6],
  certificateFrom 5277607 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3],
  certificateFrom 5285799 [1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3],
  certificateFrom 5301063 [1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3],
  certificateFrom 5308519 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4],
  certificateFrom 5316711 [1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4],
  certificateFrom 5324967 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 4, 4],
  certificateFrom 5350727 [1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4],
  certificateFrom 5352679 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3],
  certificateFrom 5356647 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6],
  certificateFrom 5360103 [1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4],
  certificateFrom 5360871 [1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3],
  certificateFrom 5364455 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5],
  certificateFrom 5364839 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4],
  certificateFrom 5370727 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6],
  certificateFrom 5378887 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4],
  certificateFrom 5379687 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5],
  certificateFrom 5384359 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 3, 3],
  certificateFrom 5387079 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4],
  certificateFrom 5393767 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3],
  certificateFrom 5402343 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4],
  certificateFrom 5403111 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3],
  certificateFrom 5410535 [1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4],
  certificateFrom 5417191 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5],
  certificateFrom 5424231 [1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3],
  certificateFrom 5466471 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3],
  certificateFrom 5473895 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4],
  certificateFrom 5474663 [1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3],
  certificateFrom 5478567 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 1, 4],
  certificateFrom 5486759 [1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 1, 4],
  certificateFrom 5488711 [1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 1, 5],
  certificateFrom 5497319 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4],
  certificateFrom 5502055 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4],
  certificateFrom 5505511 [1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4],
  certificateFrom 5510247 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4],
  certificateFrom 5516135 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4],
  certificateFrom 5524327 [1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4],
  certificateFrom 5530951 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5]]

private theorem checked05 : ∀ c ∈ cs05, Accepted c := by
  decide +kernel

private def cs06 : List Certificate :=
[  certificateFrom 5530983 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5],
  certificateFrom 5539143 [1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5],
  certificateFrom 5540327 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5],
  certificateFrom 5543079 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 1, 6],
  certificateFrom 5547335 [1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3],
  certificateFrom 5548519 [1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5],
  certificateFrom 5553255 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3],
  certificateFrom 5556711 [1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3],
  certificateFrom 5559111 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7],
  certificateFrom 5561447 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3],
  certificateFrom 5567335 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3],
  certificateFrom 5568871 [1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4],
  certificateFrom 5575527 [1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3],
  certificateFrom 5594279 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 3, 3],
  certificateFrom 5595879 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6],
  certificateFrom 5598951 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3],
  certificateFrom 5603655 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3],
  certificateFrom 5604071 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4],
  certificateFrom 5607143 [1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3],
  certificateFrom 5611879 [1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5],
  certificateFrom 5619303 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4],
  certificateFrom 5623655 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7],
  certificateFrom 5625191 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4],
  certificateFrom 5630631 [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 1, 5],
  certificateFrom 5638055 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4],
  certificateFrom 5653351 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4],
  certificateFrom 5654119 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5],
  certificateFrom 5655271 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3],
  certificateFrom 5661543 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4],
  certificateFrom 5662311 [1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5],
  certificateFrom 5670503 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3],
  certificateFrom 5676391 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3],
  certificateFrom 5682279 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7],
  certificateFrom 5700199 [1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4],
  certificateFrom 5704551 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5],
  certificateFrom 5713127 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6],
  certificateFrom 5717863 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6],
  certificateFrom 5719783 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5],
  certificateFrom 5720167 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4],
  certificateFrom 5720903 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3],
  certificateFrom 5720935 [1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3],
  certificateFrom 5726055 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4],
  certificateFrom 5728327 [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 4],
  certificateFrom 5729095 [1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3],
  certificateFrom 5732679 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5],
  certificateFrom 5739687 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 4, 3],
  certificateFrom 5744807 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 1, 6],
  certificateFrom 5763559 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6],
  certificateFrom 5764327 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3],
  certificateFrom 5770567 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4]]

private theorem checked06 : ∀ c ∈ cs06, Accepted c := by
  decide +kernel

private def cs07 : List Certificate :=
[  certificateFrom 5771335 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 3],
  certificateFrom 5778759 [1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4],
  certificateFrom 5785415 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5],
  certificateFrom 5792487 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3],
  certificateFrom 5800679 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3],
  certificateFrom 5805415 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5],
  certificateFrom 5813607 [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5],
  certificateFrom 5813991 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4],
  certificateFrom 5819495 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7],
  certificateFrom 5821799 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3],
  certificateFrom 5865543 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 1, 4],
  certificateFrom 5870247 [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 4],
  certificateFrom 5871463 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4],
  certificateFrom 5873735 [1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 1, 4],
  certificateFrom 5880423 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5],
  certificateFrom 5888615 [1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5],
  certificateFrom 5896807 [1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3],
  certificateFrom 5906279 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5],
  certificateFrom 5908551 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 1, 5],
  certificateFrom 5909735 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3],
  certificateFrom 5912487 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4],
  certificateFrom 5913255 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 3, 3],
  certificateFrom 5914471 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3],
  certificateFrom 5916743 [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 1, 5],
  certificateFrom 5920679 [1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4],
  certificateFrom 5921511 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5],
  certificateFrom 5921895 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4],
  certificateFrom 5922663 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3],
  certificateFrom 5924935 [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 3],
  certificateFrom 5933223 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 1, 5],
  certificateFrom 5941415 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 4, 3],
  certificateFrom 5942631 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5],
  certificateFrom 5951975 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5],
  certificateFrom 5953127 [1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3],
  certificateFrom 5954727 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 6],
  certificateFrom 5959399 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4],
  certificateFrom 5960167 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3],
  certificateFrom 5962919 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 2, 4],
  certificateFrom 5964103 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6],
  certificateFrom 5967175 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3],
  certificateFrom 5972295 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4],
  certificateFrom 5975367 [1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3],
  certificateFrom 5988711 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4],
  certificateFrom 5990631 [1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3],
  certificateFrom 5994215 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5],
  certificateFrom 5995367 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3],
  certificateFrom 5996903 [1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4],
  certificateFrom 6002407 [1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5],
  certificateFrom 6002791 [1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4],
  certificateFrom 6003559 [1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3]]

private theorem checked07 : ∀ c ∈ cs07, Accepted c := by
  decide +kernel

private def cs08 : List Certificate :=
[  certificateFrom 6007463 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 1, 4],
  certificateFrom 6010599 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3],
  certificateFrom 6015655 [1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 1, 4],
  certificateFrom 6015719 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6],
  certificateFrom 6023495 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3],
  certificateFrom 6030951 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4],
  certificateFrom 6036839 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6],
  certificateFrom 6039143 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4],
  certificateFrom 6045031 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4],
  certificateFrom 6050471 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 1, 5],
  certificateFrom 6058663 [1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 1, 5],
  certificateFrom 6066855 [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 3],
  certificateFrom 6081351 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6],
  certificateFrom 6088007 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5],
  certificateFrom 6097383 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5],
  certificateFrom 6100903 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5],
  certificateFrom 6104423 [1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3],
  certificateFrom 6116519 [1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 1, 4],
  certificateFrom 6117287 [1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3],
  certificateFrom 6124775 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6],
  certificateFrom 6131783 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 1, 6],
  certificateFrom 6132551 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3],
  certificateFrom 6132967 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4],
  certificateFrom 6137703 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6],
  certificateFrom 6138791 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 2, 4],
  certificateFrom 6145895 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4],
  certificateFrom 6146983 [1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 2, 4],
  certificateFrom 6151335 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 3],
  certificateFrom 6159527 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 2, 3],
  certificateFrom 6160711 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3],
  certificateFrom 6161127 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4],
  certificateFrom 6164647 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 4, 4],
  certificateFrom 6168903 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3],
  certificateFrom 6172839 [1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 2, 4],
  certificateFrom 6178279 [1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5],
  certificateFrom 6182215 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4],
  certificateFrom 6182247 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4],
  certificateFrom 6183015 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5],
  certificateFrom 6190439 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4],
  certificateFrom 6191207 [1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5],
  certificateFrom 6199399 [1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3],
  certificateFrom 6204135 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5],
  certificateFrom 6211175 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7],
  certificateFrom 6212327 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3],
  certificateFrom 6233447 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3],
  certificateFrom 6241639 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3],
  certificateFrom 6255719 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3],
  certificateFrom 6261607 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5],
  certificateFrom 6273703 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 1, 6],
  certificateFrom 6277959 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3]]

private theorem checked08 : ∀ c ∈ cs08, Accepted c := by
  decide +kernel

private def cs09 : List Certificate :=
[  certificateFrom 6283111 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4],
  certificateFrom 6286567 [1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4],
  certificateFrom 6289735 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5],
  certificateFrom 6290151 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8],
  certificateFrom 6293223 [1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3],
  certificateFrom 6318247 [1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 4],
  certificateFrom 6320199 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 1, 5],
  certificateFrom 6321383 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3],
  certificateFrom 6326119 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5],
  certificateFrom 6327623 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4],
  certificateFrom 6328391 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 3],
  certificateFrom 6329575 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3],
  certificateFrom 6334311 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3],
  certificateFrom 6335399 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 2, 3],
  certificateFrom 6336999 [1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4],
  certificateFrom 6342503 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3],
  certificateFrom 6343591 [1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 3],
  certificateFrom 6353063 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 1, 5],
  certificateFrom 6355815 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6],
  certificateFrom 6358855 [1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3],
  certificateFrom 6362439 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5],
  certificateFrom 6362471 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7],
  certificateFrom 6369447 [1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 2, 3],
  certificateFrom 6370631 [1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5],
  certificateFrom 6371047 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4],
  certificateFrom 6372967 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3],
  certificateFrom 6378823 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3],
  certificateFrom 6379239 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4],
  certificateFrom 6381159 [1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3],
  certificateFrom 6383943 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6],
  certificateFrom 6384743 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5],
  certificateFrom 6391719 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3],
  certificateFrom 6399911 [1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3],
  certificateFrom 6400359 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4],
  certificateFrom 6422631 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4],
  certificateFrom 6430823 [1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4],
  certificateFrom 6437479 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5],
  certificateFrom 6439079 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 2, 6],
  certificateFrom 6462119 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 1, 5],
  certificateFrom 6463335 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7],
  certificateFrom 6465607 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 2, 5],
  certificateFrom 6470311 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 4, 3],
  certificateFrom 6490279 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 2, 5],
  certificateFrom 6492999 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6],
  certificateFrom 6499687 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7],
  certificateFrom 6501191 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4],
  certificateFrom 6501223 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4],
  certificateFrom 6509031 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5],
  certificateFrom 6519975 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 3, 4],
  certificateFrom 6529351 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4]]

private theorem checked09 : ∀ c ∈ cs09, Accepted c := by
  decide +kernel

private def cs10 : List Certificate :=
[  certificateFrom 6546503 [1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 1, 5],
  certificateFrom 6551271 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7],
  certificateFrom 6552423 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3],
  certificateFrom 6555111 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4],
  certificateFrom 6563303 [1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4],
  certificateFrom 6572359 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5],
  certificateFrom 6580551 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3],
  certificateFrom 6589159 [1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4],
  certificateFrom 6592679 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 2, 4],
  certificateFrom 6600871 [1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 2, 4],
  certificateFrom 6602087 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4],
  certificateFrom 6607527 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 2, 5],
  certificateFrom 6611431 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4],
  certificateFrom 6616167 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6],
  certificateFrom 6619239 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3],
  certificateFrom 6619623 [1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4],
  certificateFrom 6624359 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4],
  certificateFrom 6627431 [1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3],
  certificateFrom 6630247 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6],
  certificateFrom 6632167 [1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5],
  certificateFrom 6635687 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 5, 3],
  certificateFrom 6654791 [1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4],
  certificateFrom 6657959 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5],
  certificateFrom 6658375 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8],
  certificateFrom 6661447 [1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3],
  certificateFrom 6670823 [1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3],
  certificateFrom 6675559 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3],
  certificateFrom 6682983 [1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4],
  certificateFrom 6688423 [1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 1, 5],
  certificateFrom 6689607 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3],
  certificateFrom 6690023 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4],
  certificateFrom 6695847 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 3, 4],
  certificateFrom 6697799 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3],
  certificateFrom 6702951 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4],
  certificateFrom 6705223 [1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 1, 4],
  certificateFrom 6713063 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3],
  certificateFrom 6721255 [1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3],
  certificateFrom 6733415 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6],
  certificateFrom 6739271 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4],
  certificateFrom 6740071 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5],
  certificateFrom 6747463 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4],
  certificateFrom 6752167 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6],
  certificateFrom 6761191 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5],
  certificateFrom 6767463 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6],
  certificateFrom 6775655 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4],
  certificateFrom 6784615 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3],
  certificateFrom 6789287 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 2, 3],
  certificateFrom 6797479 [1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 2, 3],
  certificateFrom 6808039 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3],
  certificateFrom 6812775 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3]]

private theorem checked10 : ∀ c ∈ cs10, Accepted c := by
  decide +kernel

private def cs11 : List Certificate :=
[  certificateFrom 6816231 [1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3],
  certificateFrom 6820967 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3],
  certificateFrom 6826855 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3],
  certificateFrom 6834279 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4],
  certificateFrom 6835047 [1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3],
  certificateFrom 6847143 [1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 1, 4],
  certificateFrom 6855399 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4],
  certificateFrom 6863207 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5],
  certificateFrom 6871399 [1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5],
  certificateFrom 6877255 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 2, 5],
  certificateFrom 6879591 [1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3],
  certificateFrom 6883175 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7],
  certificateFrom 6910119 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 2, 5],
  certificateFrom 6914791 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3],
  certificateFrom 6919495 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7],
  certificateFrom 6923335 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 1, 4],
  certificateFrom 6929255 [1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4],
  certificateFrom 6930023 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3],
  certificateFrom 6931527 [1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 4],
  certificateFrom 6935911 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3],
  certificateFrom 6941799 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5],
  certificateFrom 6948775 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3],
  certificateFrom 6955879 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5],
  certificateFrom 6957383 [1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4],
  certificateFrom 6964071 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3],
  certificateFrom 6972263 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3],
  certificateFrom 6979655 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 4],
  certificateFrom 6979687 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4],
  certificateFrom 6985575 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4],
  certificateFrom 6987847 [1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 2, 4],
  certificateFrom 6991015 [1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 1, 5],
  certificateFrom 7000391 [1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5],
  certificateFrom 7008999 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4],
  certificateFrom 7010919 [1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3],
  certificateFrom 7014503 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5],
  certificateFrom 7017191 [1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4],
  certificateFrom 7019175 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 2, 5],
  certificateFrom 7022695 [1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5],
  certificateFrom 7026599 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6],
  certificateFrom 7030887 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3],
  certificateFrom 7036007 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6],
  certificateFrom 7036775 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3],
  certificateFrom 7039047 [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 3, 3],
  certificateFrom 7058247 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4],
  certificateFrom 7064935 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5],
  certificateFrom 7065255 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 1, 4],
  certificateFrom 7073447 [1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 1, 4],
  certificateFrom 7073511 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6],
  certificateFrom 7081287 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3],
  certificateFrom 7089479 [1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3]]

private theorem checked11 : ∀ c ∈ cs11, Accepted c := by
  decide +kernel

private def cs12 : List Certificate :=
[  certificateFrom 7102823 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4],
  certificateFrom 7111015 [1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4],
  certificateFrom 7114599 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8],
  certificateFrom 7121575 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4],
  certificateFrom 7124711 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3],
  certificateFrom 7129415 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5],
  certificateFrom 7129767 [1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 2, 4],
  certificateFrom 7145063 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6],
  certificateFrom 7149735 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 3, 4],
  certificateFrom 7153255 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4],
  certificateFrom 7161063 [1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5],
  certificateFrom 7165799 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5],
  certificateFrom 7168487 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4],
  certificateFrom 7173991 [1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5],
  certificateFrom 7176263 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 3],
  certificateFrom 7180967 [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3],
  certificateFrom 7181415 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4],
  certificateFrom 7182183 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3],
  certificateFrom 7184455 [1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2, 3],
  certificateFrom 7223207 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3],
  certificateFrom 7223623 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4],
  certificateFrom 7224423 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5],
  certificateFrom 7230631 [1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 2, 4],
  certificateFrom 7231399 [1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3],
  certificateFrom 7232615 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3],
  certificateFrom 7270119 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3],
  certificateFrom 7273639 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 3, 3],
  certificateFrom 7275239 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6],
  certificateFrom 7278759 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 2, 6],
  certificateFrom 7283015 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3],
  certificateFrom 7296359 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6],
  certificateFrom 7299431 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3],
  certificateFrom 7304551 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4],
  certificateFrom 7306855 [1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4],
  certificateFrom 7307623 [1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3],
  certificateFrom 7310439 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8],
  certificateFrom 7313511 [1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3],
  certificateFrom 7318183 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 2, 3],
  certificateFrom 7325607 [1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4],
  certificateFrom 7326375 [1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 2, 3],
  certificateFrom 7332711 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4],
  certificateFrom 7341671 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3],
  certificateFrom 7349863 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3],
  certificateFrom 7355751 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3],
  certificateFrom 7367847 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 1, 4],
  certificateFrom 7368615 [1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 1, 5],
  certificateFrom 7376039 [1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 1, 4],
  certificateFrom 7377223 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4],
  certificateFrom 7385415 [1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4],
  certificateFrom 7391335 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4]]

private theorem checked12 : ∀ c ∈ cs12, Accepted c := by
  decide +kernel

private def cs13 : List Certificate :=
[  certificateFrom 7397223 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6],
  certificateFrom 7399527 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4],
  certificateFrom 7400679 [1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4],
  certificateFrom 7410855 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 1, 5],
  certificateFrom 7419047 [1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 1, 5],
  certificateFrom 7420263 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5],
  certificateFrom 7424167 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 4, 4],
  certificateFrom 7427239 [1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 3],
  certificateFrom 7432359 [1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 2, 4],
  certificateFrom 7441735 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6],
  certificateFrom 7442919 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4],
  certificateFrom 7443687 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3],
  certificateFrom 7449511 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 3, 3],
  certificateFrom 7451111 [1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4],
  certificateFrom 7456615 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3],
  certificateFrom 7457703 [1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 3, 3],
  certificateFrom 7463655 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5],
  certificateFrom 7471847 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3],
  certificateFrom 7475367 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 5, 3],
  certificateFrom 7483559 [1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 3, 3],
  certificateFrom 7485159 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6],
  certificateFrom 7492935 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3],
  certificateFrom 7492967 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3],
  certificateFrom 7493351 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4],
  certificateFrom 7501159 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3],
  certificateFrom 7512935 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7],
  certificateFrom 7514471 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4],
  certificateFrom 7529287 [1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5],
  certificateFrom 7536711 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 4],
  certificateFrom 7537895 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4],
  certificateFrom 7542631 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4],
  certificateFrom 7546087 [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4],
  certificateFrom 7550823 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4],
  certificateFrom 7561383 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 5, 4],
  certificateFrom 7569575 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 1, 4],
  certificateFrom 7571559 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7],
  certificateFrom 7580903 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5],
  certificateFrom 7589095 [1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5],
  certificateFrom 7593831 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3],
  certificateFrom 7597287 [1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3],
  certificateFrom 7609447 [1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4],
  certificateFrom 7612583 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 1, 5],
  certificateFrom 7615335 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4],
  certificateFrom 7621991 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5],
  certificateFrom 7628967 [1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 2, 3],
  certificateFrom 7631335 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5],
  certificateFrom 7634087 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 6],
  certificateFrom 7638343 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3],
  certificateFrom 7643463 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6],
  certificateFrom 7646951 [1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4]]

private theorem checked13 : ∀ c ∈ cs13, Accepted c := by
  decide +kernel

private def cs14 : List Certificate :=
[  certificateFrom 7647719 [1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3],
  certificateFrom 7652455 [1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5],
  certificateFrom 7659879 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4],
  certificateFrom 7669223 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4],
  certificateFrom 7677415 [1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4],
  certificateFrom 7678631 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 3, 4],
  certificateFrom 7681767 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3],
  certificateFrom 7689959 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3],
  certificateFrom 7694695 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5],
  certificateFrom 7695079 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4],
  certificateFrom 7702887 [1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5],
  certificateFrom 7703271 [1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4],
  certificateFrom 7710311 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4],
  certificateFrom 7711079 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3],
  certificateFrom 7716199 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6],
  certificateFrom 7722855 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7],
  certificateFrom 7733351 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3],
  certificateFrom 7741543 [1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3],
  certificateFrom 7745447 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 1, 4],
  certificateFrom 7753639 [1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 4],
  certificateFrom 7760743 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4],
  certificateFrom 7768903 [1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4],
  certificateFrom 7781479 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5],
  certificateFrom 7795559 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5],
  certificateFrom 7803751 [1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5],
  certificateFrom 7804135 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6],
  certificateFrom 7809959 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 1, 6],
  certificateFrom 7811143 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 4, 4],
  certificateFrom 7811911 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3],
  certificateFrom 7811943 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3],
  certificateFrom 7817063 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6],
  certificateFrom 7819335 [1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 2, 4],
  certificateFrom 7822503 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 5],
  certificateFrom 7830695 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 3],
  certificateFrom 7831879 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5],
  certificateFrom 7840071 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3],
  certificateFrom 7848679 [1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4],
  certificateFrom 7853383 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6],
  certificateFrom 7860071 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9],
  certificateFrom 7861575 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4],
  certificateFrom 7861607 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4],
  certificateFrom 7865831 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3],
  certificateFrom 7874023 [1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3],
  certificateFrom 7875687 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4],
  certificateFrom 7883495 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5],
  certificateFrom 7899879 [1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3],
  certificateFrom 7903399 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 3, 3],
  certificateFrom 7904615 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5],
  certificateFrom 7906119 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4],
  certificateFrom 7911591 [1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 3, 3]]

private theorem checked14 : ∀ c ∈ cs14, Accepted c := by
  decide +kernel

private def cs15 : List Certificate :=
[  certificateFrom 7912807 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3],
  certificateFrom 7914311 [1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4],
  certificateFrom 7922151 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3],
  certificateFrom 7930343 [1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3],
  certificateFrom 7935079 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3],
  certificateFrom 7949127 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5],
  certificateFrom 7953063 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 4, 4],
  certificateFrom 7957319 [1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5],
  certificateFrom 7961255 [1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 2, 4],
  certificateFrom 7965511 [1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3],
  certificateFrom 7967911 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 2, 5],
  certificateFrom 7969511 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6],
  certificateFrom 7990631 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8],
  certificateFrom 7992551 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5],
  certificateFrom 7993703 [1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3],
  certificateFrom 7999559 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 5],
  certificateFrom 8000743 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3],
  certificateFrom 8006567 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 4, 3],
  certificateFrom 8013671 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3],
  certificateFrom 8015175 [1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4],
  certificateFrom 8015943 [1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 3],
  certificateFrom 8020711 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5],
  certificateFrom 8029287 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4],
  certificateFrom 8037447 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 2, 4],
  certificateFrom 8037479 [1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4],
  certificateFrom 8043367 [1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4],
  certificateFrom 8045639 [1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 2, 4],
  certificateFrom 8049991 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3],
  certificateFrom 8050407 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4],
  certificateFrom 8058183 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3],
  certificateFrom 8063303 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4],
  certificateFrom 8071495 [1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4],
  certificateFrom 8071527 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4],
  certificateFrom 8079719 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4],
  certificateFrom 8086375 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3],
  certificateFrom 8093799 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6],
  certificateFrom 8123111 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4],
  certificateFrom 8131303 [1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4],
  certificateFrom 8137959 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5],
  certificateFrom 8141479 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 1, 5],
  certificateFrom 8142695 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5],
  certificateFrom 8144999 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3],
  certificateFrom 8157095 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4],
  certificateFrom 8157863 [1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 2, 3],
  certificateFrom 8166119 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3],
  certificateFrom 8169639 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 2, 5],
  certificateFrom 8172359 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6],
  certificateFrom 8172391 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4],
  certificateFrom 8179367 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 2, 4],
  certificateFrom 8180583 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4]]

private theorem checked15 : ∀ c ∈ cs15, Accepted c := by
  decide +kernel

private def cs16 : List Certificate :=
[  certificateFrom 8181351 [1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5],
  certificateFrom 8187559 [1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 2, 4],
  certificateFrom 8188391 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5],
  certificateFrom 8207527 [1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 1, 4],
  certificateFrom 8216903 [1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4],
  certificateFrom 8218855 [1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5],
  certificateFrom 8223591 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5],
  certificateFrom 8226279 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4],
  certificateFrom 8231783 [1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5],
  certificateFrom 8234055 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 2, 3],
  certificateFrom 8239975 [1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3],
  certificateFrom 8242247 [1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 3],
  certificateFrom 8251719 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5],
  certificateFrom 8251751 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7],
  certificateFrom 8263847 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 1, 6],
  certificateFrom 8268103 [1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3],
  certificateFrom 8282599 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6],
  certificateFrom 8289639 [1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4],
  certificateFrom 8290375 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 3],
  certificateFrom 8290407 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3],
  certificateFrom 8295527 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6],
  certificateFrom 8296295 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3],
  certificateFrom 8298567 [1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 3],
  certificateFrom 8319719 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3],
  certificateFrom 8327911 [1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3],
  certificateFrom 8332647 [1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5],
  certificateFrom 8337735 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6],
  certificateFrom 8352615 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7],
  certificateFrom 8360775 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5],
  certificateFrom 8368967 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3],
  certificateFrom 8375975 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 2, 3],
  certificateFrom 8377575 [1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4],
  certificateFrom 8379559 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 2, 5],
  certificateFrom 8383399 [1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 1, 4],
  certificateFrom 8384167 [1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 2, 3]]

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
[  4163943, 4170567, 4178759, 4182695, 4186951, 4189351, 4198727, 4209255, 4221031, 4233127, 4233895, 4236615, 4237383, 4238567,
  4242151, 4242535, 4245991, 4246759, 4250727, 4256615, 4262055, 4263271, 4264807, 4270247, 4279623, 4280807, 4283559, 4288231,
  4288999, 4292935, 4293735, 4296423, 4301927, 4310119, 4315239, 4318279, 4336359, 4344135, 4344167, 4344551, 4359399, 4359783,
  4360551, 4365671, 4372327, 4379303, 4391079, 4403943, 4410183, 4410215, 4418375, 4421543, 4422759, 4428967, 4429735, 4445031,
  4452423, 4453607, 4460199, 4460615, 4461415, 4463783, 4471975, 4473159, 4480167, 4481351, 4481767, 4485287, 4489543, 4489959,
  4511079, 4511847, 4516967, 4531047, 4532967, 4541159, 4545895, 4554087, 4562279, 4566951, 4582247, 4586087, 4589671, 4594343,
  4599015, 4602535, 4603751, 4606791, 4610375, 4611943, 4614215, 4614983, 4630695, 4633831, 4634983, 4642023, 4642407, 4643175,
  4647847, 4649031, 4649447, 4650215, 4656455, 4657223, 4661991, 4664647, 4673703, 4679911, 4681895, 4684647, 4692839, 4699879,
  4704583, 4712775, 4713575, 4727623, 4727655, 4740967, 4756135, 4759719, 4762791, 4772167, 4786279, 4790951, 4793703, 4794471,
  4799143, 4799207, 4806567, 4821831, 4822631, 4830823, 4836711, 4839015, 4840615, 4848807, 4849991, 4850791, 4858183, 4860135,
  4868327, 4876519, 4881255, 4888679, 4889447, 4901191, 4901223, 4901607, 4909383, 4922727, 4930919, 4931687, 4932839, 4937575,
  4944999, 4945767, 4967239, 4973927, 4978599, 4982119, 4982503, 4990311, 4995431, 4996199, 5002055, 5002087, 5010247, 5010663,
  5017671, 5018439, 5018855, 5020839, 5023591, 5024679, 5030215, 5031783, 5032871, 5048135, 5058727, 5062247, 5066599, 5068103,
  5070439, 5080999, 5089191, 5101735, 5102951, 5120487, 5125223, 5133415, 5140391, 5141607, 5159591, 5162727, 5167431, 5170919,
  5179111, 5182631, 5190823, 5190887, 5192039, 5197159, 5228359, 5230759, 5235431, 5236551, 5241703, 5244743, 5258855, 5262439,
  5267047, 5269831, 5269863, 5277607, 5285799, 5301063, 5308519, 5316711, 5324967, 5350727, 5352679, 5356647, 5360103, 5360871,
  5364455, 5364839, 5370727, 5378887, 5379687, 5384359, 5387079, 5393767, 5402343, 5403111, 5410535, 5417191, 5424231, 5466471,
  5473895, 5474663, 5478567, 5486759, 5488711, 5497319, 5502055, 5505511, 5510247, 5516135, 5524327, 5530951, 5530983, 5539143,
  5540327, 5543079, 5547335, 5548519, 5553255, 5556711, 5559111, 5561447, 5567335, 5568871, 5575527, 5594279, 5595879, 5598951,
  5603655, 5604071, 5607143, 5611879, 5619303, 5623655, 5625191, 5630631, 5638055, 5653351, 5654119, 5655271, 5661543, 5662311,
  5670503, 5676391, 5682279, 5700199, 5704551, 5713127, 5717863, 5719783, 5720167, 5720903, 5720935, 5726055, 5728327, 5729095,
  5732679, 5739687, 5744807, 5763559, 5764327, 5770567, 5771335, 5778759, 5785415, 5792487, 5800679, 5805415, 5813607, 5813991,
  5819495, 5821799, 5865543, 5870247, 5871463, 5873735, 5880423, 5888615, 5896807, 5906279, 5908551, 5909735, 5912487, 5913255,
  5914471, 5916743, 5920679, 5921511, 5921895, 5922663, 5924935, 5933223, 5941415, 5942631, 5951975, 5953127, 5954727, 5959399,
  5960167, 5962919, 5964103, 5967175, 5972295, 5975367, 5988711, 5990631, 5994215, 5995367, 5996903, 6002407, 6002791, 6003559,
  6007463, 6010599, 6015655, 6015719, 6023495, 6030951, 6036839, 6039143, 6045031, 6050471, 6058663, 6066855, 6081351, 6088007,
  6097383, 6100903, 6104423, 6116519, 6117287, 6124775, 6131783, 6132551, 6132967, 6137703, 6138791, 6145895, 6146983, 6151335,
  6159527, 6160711, 6161127, 6164647, 6168903, 6172839, 6178279, 6182215, 6182247, 6183015, 6190439, 6191207, 6199399, 6204135,
  6211175, 6212327, 6233447, 6241639, 6255719, 6261607, 6273703, 6277959, 6283111, 6286567, 6289735, 6290151, 6293223, 6318247,
  6320199, 6321383, 6326119, 6327623, 6328391, 6329575, 6334311, 6335399, 6336999, 6342503, 6343591, 6353063, 6355815, 6358855,
  6362439, 6362471, 6369447, 6370631, 6371047, 6372967, 6378823, 6379239, 6381159, 6383943, 6384743, 6391719, 6399911, 6400359,
  6422631, 6430823, 6437479, 6439079, 6462119, 6463335, 6465607, 6470311, 6490279, 6492999, 6499687, 6501191, 6501223, 6509031,
  6519975, 6529351, 6546503, 6551271, 6552423, 6555111, 6563303, 6572359, 6580551, 6589159, 6592679, 6600871, 6602087, 6607527,
  6611431, 6616167, 6619239, 6619623, 6624359, 6627431, 6630247, 6632167, 6635687, 6654791, 6657959, 6658375, 6661447, 6670823,
  6675559, 6682983, 6688423, 6689607, 6690023, 6695847, 6697799, 6702951, 6705223, 6713063, 6721255, 6733415, 6739271, 6740071,
  6747463, 6752167, 6761191, 6767463, 6775655, 6784615, 6789287, 6797479, 6808039, 6812775, 6816231, 6820967, 6826855, 6834279,
  6835047, 6847143, 6855399, 6863207, 6871399, 6877255, 6879591, 6883175, 6910119, 6914791, 6919495, 6923335, 6929255, 6930023,
  6931527, 6935911, 6941799, 6948775, 6955879, 6957383, 6964071, 6972263, 6979655, 6979687, 6985575, 6987847, 6991015, 7000391,
  7008999, 7010919, 7014503, 7017191, 7019175, 7022695, 7026599, 7030887, 7036007, 7036775, 7039047, 7058247, 7064935, 7065255,
  7073447, 7073511, 7081287, 7089479, 7102823, 7111015, 7114599, 7121575, 7124711, 7129415, 7129767, 7145063, 7149735, 7153255,
  7161063, 7165799, 7168487, 7173991, 7176263, 7180967, 7181415, 7182183, 7184455, 7223207, 7223623, 7224423, 7230631, 7231399,
  7232615, 7270119, 7273639, 7275239, 7278759, 7283015, 7296359, 7299431, 7304551, 7306855, 7307623, 7310439, 7313511, 7318183,
  7325607, 7326375, 7332711, 7341671, 7349863, 7355751, 7367847, 7368615, 7376039, 7377223, 7385415, 7391335, 7397223, 7399527,
  7400679, 7410855, 7419047, 7420263, 7424167, 7427239, 7432359, 7441735, 7442919, 7443687, 7449511, 7451111, 7456615, 7457703,
  7463655, 7471847, 7475367, 7483559, 7485159, 7492935, 7492967, 7493351, 7501159, 7512935, 7514471, 7529287, 7536711, 7537895,
  7542631, 7546087, 7550823, 7561383, 7569575, 7571559, 7580903, 7589095, 7593831, 7597287, 7609447, 7612583, 7615335, 7621991,
  7628967, 7631335, 7634087, 7638343, 7643463, 7646951, 7647719, 7652455, 7659879, 7669223, 7677415, 7678631, 7681767, 7689959,
  7694695, 7695079, 7702887, 7703271, 7710311, 7711079, 7716199, 7722855, 7733351, 7741543, 7745447, 7753639, 7760743, 7768903,
  7781479, 7795559, 7803751, 7804135, 7809959, 7811143, 7811911, 7811943, 7817063, 7819335, 7822503, 7830695, 7831879, 7840071,
  7848679, 7853383, 7860071, 7861575, 7861607, 7865831, 7874023, 7875687, 7883495, 7899879, 7903399, 7904615, 7906119, 7911591,
  7912807, 7914311, 7922151, 7930343, 7935079, 7949127, 7953063, 7957319, 7961255, 7965511, 7967911, 7969511, 7990631, 7992551,
  7993703, 7999559, 8000743, 8006567, 8013671, 8015175, 8015943, 8020711, 8029287, 8037447, 8037479, 8043367, 8045639, 8049991,
  8050407, 8058183, 8063303, 8071495, 8071527, 8079719, 8086375, 8093799, 8123111, 8131303, 8137959, 8141479, 8142695, 8144999,
  8157095, 8157863, 8166119, 8169639, 8172359, 8172391, 8179367, 8180583, 8181351, 8187559, 8188391, 8207527, 8216903, 8218855,
  8223591, 8226279, 8231783, 8234055, 8239975, 8242247, 8251719, 8251751, 8263847, 8268103, 8282599, 8289639, 8290375, 8290407,
  8295527, 8296295, 8298567, 8319719, 8327911, 8332647, 8337735, 8352615, 8360775, 8368967, 8375975, 8377575, 8379559, 8383399,
  8384167]

private theorem certificateFrom_residue (r : ℕ) (es : List ℕ) :
    (certificateFrom r es).residue = r := by
  rfl

private theorem residue_map :
    certificates.map Certificate.residue = rawResidues := by
  simp only [certificates, cs01, cs02, cs03, cs04, cs05, cs06, cs07, cs08, cs09, cs10, cs11, cs12, cs13, cs14, cs15, cs16, rawResidues,
    List.map_append, List.map_cons, List.map_nil, certificateFrom_residue,
    List.cons_append, List.nil_append]

private theorem target_mem_iff (r : ℕ) :
    r ∈ syracuseSevenMod32New23Step13Chunk02Classes ↔ r ∈ rawResidues := by
  simp only [syracuseSevenMod32New23Step13Chunk02Classes, rawResidues,
    Finset.mem_insert, Finset.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]

end Session67Parents

theorem solution (n : ℕ)
    (h : n % 8388608 ∈ syracuseSevenMod32New23Step13Chunk02Classes) :
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
