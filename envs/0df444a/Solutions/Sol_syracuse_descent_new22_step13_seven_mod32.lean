-- Prove2me | solution 1 for syracuse_descent_new22_step13_seven_mod32
-- status  : ACCEPTED   (prove)
-- author  : @FakeMink
-- created : 2026-10-01T17:53:56.575985+00:00
-- url     : https://prove2.me/submissions/689bc168-72a0-4614-97af-626e5b14d470

import Definitions.Def_syracuseSevenMod32New22Step13Classes
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
  Valid 4194304 c.residue c.endA c.endB c.trace ∧
  c.trace.length = 13 ∧ c.endA ≤ 4194304 ∧ c.endB < c.residue

instance (c : Certificate) : Decidable (Accepted c) := by
  unfold Accepted
  infer_instance

def residues (cs : List Certificate) : List ℕ := cs.map Certificate.residue

theorem descent_of_accepted {c : Certificate} (h : Accepted c) (k : ℕ) :
    syracuseStep^[13] (4194304 * k + c.residue) < 4194304 * k + c.residue := by
  rcases h with ⟨hvalid, hlength, ha, hb⟩
  simpa only [hlength] using AffineTrace.strict_descent hvalid ha hb k

theorem descent_of_residue {c : Certificate} (h : Accepted c)
    (n : ℕ) (hn : n % 4194304 = c.residue) : syracuseStep^[13] n < n := by
  have hform : n = 4194304 * (n / 4194304) + c.residue := by omega
  rw [hform]
  exact descent_of_accepted h (n / 4194304)

/-- The proof consumes finite, kernel-checked certificate acceptance, not search output. -/
theorem descent_of_mem (cs : List Certificate) (hchecked : ∀ c ∈ cs, Accepted c)
    (n : ℕ) (h : n % 4194304 ∈ residues cs) : syracuseStep^[13] n < n := by
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

private def cs01 : List Certificate :=
[  certificateFrom 1767 [1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2],
  certificateFrom 18023 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3],
  certificateFrom 18791 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2],
  certificateFrom 23911 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5],
  certificateFrom 26215 [1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3],
  certificateFrom 26791 [1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3],
  certificateFrom 28743 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 1, 4],
  certificateFrom 29927 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2],
  certificateFrom 32839 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4],
  certificateFrom 32871 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4],
  certificateFrom 34023 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2],
  certificateFrom 34663 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4],
  certificateFrom 36167 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3],
  certificateFrom 36935 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 2],
  certificateFrom 38119 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2],
  certificateFrom 38759 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4],
  certificateFrom 41031 [1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 1, 4],
  certificateFrom 42855 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2],
  certificateFrom 43943 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 2, 2],
  certificateFrom 44967 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 1, 5],
  certificateFrom 45543 [1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3],
  certificateFrom 46951 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2],
  certificateFrom 49223 [1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2],
  certificateFrom 51047 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2],
  certificateFrom 52135 [1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2],
  certificateFrom 60263 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5],
  certificateFrom 61607 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 1, 4],
  certificateFrom 64359 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5],
  certificateFrom 65703 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 4, 2],
  certificateFrom 67399 [1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2],
  certificateFrom 68455 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3],
  certificateFrom 70983 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4],
  certificateFrom 71015 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6],
  certificateFrom 77991 [1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 2, 2],
  certificateFrom 79175 [1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4],
  certificateFrom 79591 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3],
  certificateFrom 81511 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2],
  certificateFrom 83687 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3],
  certificateFrom 87367 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2],
  certificateFrom 87783 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3],
  certificateFrom 88391 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5],
  certificateFrom 89703 [1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2],
  certificateFrom 91463 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2],
  certificateFrom 92487 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5],
  certificateFrom 93287 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4],
  certificateFrom 96167 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2],
  certificateFrom 96583 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3],
  certificateFrom 99655 [1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2],
  certificateFrom 100263 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2],
  certificateFrom 100839 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2]]

private theorem checked01 : ∀ c ∈ cs01, Accepted c := by
  decide +kernel

private def cs02 : List Certificate :=
[  certificateFrom 108455 [1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2],
  certificateFrom 108903 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3],
  certificateFrom 109031 [1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2],
  certificateFrom 111431 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4],
  certificateFrom 111847 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5],
  certificateFrom 112999 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3],
  certificateFrom 119655 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2],
  certificateFrom 121191 [1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3],
  certificateFrom 124775 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7],
  certificateFrom 131175 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3],
  certificateFrom 138407 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 5, 2],
  certificateFrom 139367 [1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3],
  certificateFrom 146023 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4],
  certificateFrom 146599 [1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 3, 2],
  certificateFrom 147623 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 2, 5],
  certificateFrom 147783 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2],
  certificateFrom 149319 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3],
  certificateFrom 155975 [1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2],
  certificateFrom 156007 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4],
  certificateFrom 164199 [1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4],
  certificateFrom 169319 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3],
  certificateFrom 170663 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4],
  certificateFrom 171879 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6],
  certificateFrom 172391 [1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2],
  certificateFrom 174151 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 2, 4],
  certificateFrom 174759 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 4],
  certificateFrom 177511 [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3],
  certificateFrom 178855 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 4, 2],
  certificateFrom 182951 [1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 1, 4],
  certificateFrom 191143 [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2],
  certificateFrom 198823 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4],
  certificateFrom 201543 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5],
  certificateFrom 202919 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 2, 4],
  certificateFrom 205639 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5],
  certificateFrom 206439 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4],
  certificateFrom 208231 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6],
  certificateFrom 209735 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3],
  certificateFrom 209767 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3],
  certificateFrom 217575 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4],
  certificateFrom 220519 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2],
  certificateFrom 221671 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4],
  certificateFrom 222823 [1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2],
  certificateFrom 228519 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 3, 3],
  certificateFrom 228711 [1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2],
  certificateFrom 234599 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4],
  certificateFrom 237895 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3],
  certificateFrom 240807 [1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3],
  certificateFrom 241575 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 4, 2],
  certificateFrom 244327 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3],
  certificateFrom 250183 [1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3]]

private theorem checked02 : ∀ c ∈ cs02, Accepted c := by
  decide +kernel

private def cs03 : List Certificate :=
[  certificateFrom 252519 [1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3],
  certificateFrom 255047 [1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 1, 4],
  certificateFrom 256871 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2],
  certificateFrom 259815 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6],
  certificateFrom 260967 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2],
  certificateFrom 263655 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3],
  certificateFrom 265063 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2],
  certificateFrom 270183 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3],
  certificateFrom 271847 [1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3],
  certificateFrom 272455 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 2, 3],
  certificateFrom 272487 [1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3],
  certificateFrom 276807 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4],
  certificateFrom 280647 [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 2, 3],
  certificateFrom 280903 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4],
  certificateFrom 283815 [1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 1, 4],
  certificateFrom 284999 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2],
  certificateFrom 285415 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3],
  certificateFrom 289095 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2],
  certificateFrom 293191 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2],
  certificateFrom 297127 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 2, 3],
  certificateFrom 297703 [1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3],
  certificateFrom 301223 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 2, 3],
  certificateFrom 306535 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3],
  certificateFrom 308455 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2],
  certificateFrom 309415 [1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 2, 3],
  certificateFrom 310631 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3],
  certificateFrom 314727 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3],
  certificateFrom 315879 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3],
  certificateFrom 316071 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 2, 4],
  certificateFrom 316647 [1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2],
  certificateFrom 319975 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3],
  certificateFrom 322471 [1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 3, 2],
  certificateFrom 324711 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5],
  certificateFrom 327783 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2],
  certificateFrom 328167 [1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3],
  certificateFrom 328807 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5],
  certificateFrom 332903 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3],
  certificateFrom 335975 [1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2],
  certificateFrom 338791 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5],
  certificateFrom 340711 [1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4],
  certificateFrom 344231 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 5, 2],
  certificateFrom 348327 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 3, 2],
  certificateFrom 357735 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4],
  certificateFrom 358119 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3],
  certificateFrom 363335 [1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3],
  certificateFrom 366311 [1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3],
  certificateFrom 366503 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4],
  certificateFrom 366919 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7],
  certificateFrom 369991 [1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2],
  certificateFrom 374119 [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2]]

private theorem checked03 : ∀ c ∈ cs03, Accepted c := by
  decide +kernel

private def cs04 : List Certificate :=
[  certificateFrom 379239 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5],
  certificateFrom 379367 [1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2],
  certificateFrom 384103 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2],
  certificateFrom 385895 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4],
  certificateFrom 391527 [1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3],
  certificateFrom 396967 [1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 1, 4],
  certificateFrom 398151 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2],
  certificateFrom 398567 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3],
  certificateFrom 402247 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2],
  certificateFrom 404391 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 3, 3],
  certificateFrom 406343 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2],
  certificateFrom 410855 [1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3],
  certificateFrom 411495 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3],
  certificateFrom 413767 [1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 1, 3],
  certificateFrom 414375 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 2, 3],
  certificateFrom 421607 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2],
  certificateFrom 422567 [1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 2, 3],
  certificateFrom 423783 [1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3],
  certificateFrom 429799 [1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2],
  certificateFrom 440935 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2],
  certificateFrom 441959 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5],
  certificateFrom 444519 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4],
  certificateFrom 447815 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3],
  certificateFrom 448615 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4],
  certificateFrom 449127 [1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2],
  certificateFrom 451911 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3],
  certificateFrom 453863 [1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4],
  certificateFrom 456007 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3],
  certificateFrom 456615 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5],
  certificateFrom 460711 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5],
  certificateFrom 461287 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3],
  certificateFrom 464807 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3],
  certificateFrom 465639 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6],
  certificateFrom 469063 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 2, 2],
  certificateFrom 469735 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4],
  certificateFrom 474215 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3],
  certificateFrom 476007 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5],
  certificateFrom 477255 [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2],
  certificateFrom 477351 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 3, 4],
  certificateFrom 480071 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5],
  certificateFrom 480103 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5],
  certificateFrom 484199 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3],
  certificateFrom 485543 [1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 1, 4],
  certificateFrom 493159 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2],
  certificateFrom 493735 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2],
  certificateFrom 496103 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4],
  certificateFrom 497255 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2],
  certificateFrom 497831 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2],
  certificateFrom 504295 [1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4],
  certificateFrom 505447 [1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2]]

private theorem checked04 : ∀ c ∈ cs04, Accepted c := by
  decide +kernel

private def cs05 : List Certificate :=
[  certificateFrom 506023 [1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 2, 2],
  certificateFrom 512487 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2],
  certificateFrom 516583 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2],
  certificateFrom 521319 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2],
  certificateFrom 524775 [1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2],
  certificateFrom 525415 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2],
  certificateFrom 529511 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2],
  certificateFrom 534759 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2],
  certificateFrom 535399 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2],
  certificateFrom 542183 [1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3],
  certificateFrom 542823 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3],
  certificateFrom 542951 [1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2],
  certificateFrom 543591 [1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2],
  certificateFrom 544615 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5],
  certificateFrom 546535 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4],
  certificateFrom 546919 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3],
  certificateFrom 555111 [1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3],
  certificateFrom 555687 [1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 1, 3],
  certificateFrom 562919 [1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2],
  certificateFrom 563943 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3],
  certificateFrom 567655 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4],
  certificateFrom 568039 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3],
  certificateFrom 571751 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4],
  certificateFrom 575847 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2],
  certificateFrom 579943 [1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4],
  certificateFrom 585799 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 2, 4],
  certificateFrom 588135 [1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2],
  certificateFrom 589895 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4],
  certificateFrom 591719 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6],
  certificateFrom 595815 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4],
  certificateFrom 603239 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5],
  certificateFrom 606311 [1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2],
  certificateFrom 610983 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 2, 2],
  certificateFrom 614567 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 4, 4],
  certificateFrom 618407 [1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 3],
  certificateFrom 618663 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 2, 4],
  certificateFrom 619175 [1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2],
  certificateFrom 623335 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2],
  certificateFrom 625511 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3],
  certificateFrom 628039 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6],
  certificateFrom 631879 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 1, 3],
  certificateFrom 637799 [1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3],
  certificateFrom 638567 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2],
  certificateFrom 640071 [1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 3],
  certificateFrom 644455 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2],
  certificateFrom 648551 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2],
  certificateFrom 650343 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4],
  certificateFrom 653223 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2],
  certificateFrom 653639 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3],
  certificateFrom 656743 [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2]]

private theorem checked05 : ∀ c ∈ cs05, Accepted c := by
  decide +kernel

private def cs06 : List Certificate :=
[  certificateFrom 657319 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2],
  certificateFrom 660647 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 1, 3],
  certificateFrom 661415 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2],
  certificateFrom 664423 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4],
  certificateFrom 665927 [1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3],
  certificateFrom 668519 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4],
  certificateFrom 668839 [1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3],
  certificateFrom 672615 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2],
  certificateFrom 676679 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2],
  certificateFrom 676711 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2],
  certificateFrom 680807 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2],
  certificateFrom 684103 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 2, 3],
  certificateFrom 684871 [1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2],
  certificateFrom 688199 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 3],
  certificateFrom 688231 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3],
  certificateFrom 690023 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3],
  certificateFrom 694119 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3],
  certificateFrom 696391 [1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 2, 3],
  certificateFrom 699559 [1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 1, 4],
  certificateFrom 708775 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 1, 5],
  certificateFrom 708935 [1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4],
  certificateFrom 713063 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4],
  certificateFrom 713447 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3],
  certificateFrom 716967 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 2, 3],
  certificateFrom 717543 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3],
  certificateFrom 719463 [1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2],
  certificateFrom 722407 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4],
  certificateFrom 723047 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4],
  certificateFrom 725735 [1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3],
  certificateFrom 726343 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3],
  certificateFrom 727719 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 2, 4],
  certificateFrom 730599 [1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4],
  certificateFrom 731239 [1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4],
  certificateFrom 731815 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 2, 4],
  certificateFrom 734535 [1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3],
  certificateFrom 735143 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5],
  certificateFrom 738791 [1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2],
  certificateFrom 739431 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2],
  certificateFrom 740455 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5],
  certificateFrom 741223 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2],
  certificateFrom 743527 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2],
  certificateFrom 744551 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5],
  certificateFrom 745319 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2],
  certificateFrom 747591 [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 3, 2],
  certificateFrom 748263 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4],
  certificateFrom 748647 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3],
  certificateFrom 751719 [1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2],
  certificateFrom 754535 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7],
  certificateFrom 756455 [1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4],
  certificateFrom 763495 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4]]

private theorem checked06 : ∀ c ∈ cs06, Accepted c := by
  decide +kernel

private def cs07 : List Certificate :=
[  certificateFrom 764647 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2],
  certificateFrom 766791 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3],
  certificateFrom 773479 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4],
  certificateFrom 773799 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 1, 3],
  certificateFrom 776359 [1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2],
  certificateFrom 779079 [1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3],
  certificateFrom 781991 [1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3],
  certificateFrom 782055 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5],
  certificateFrom 789831 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2],
  certificateFrom 795111 [1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2],
  certificateFrom 798023 [1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2],
  certificateFrom 799847 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2],
  certificateFrom 801383 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3],
  certificateFrom 808039 [1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2],
  certificateFrom 811367 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3],
  certificateFrom 819559 [1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3],
  certificateFrom 822087 [1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4],
  certificateFrom 823143 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7],
  certificateFrom 826023 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 2, 3],
  certificateFrom 829511 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 3, 3],
  certificateFrom 830119 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3],
  certificateFrom 830695 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3],
  certificateFrom 833255 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2],
  certificateFrom 833863 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6],
  certificateFrom 837351 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2],
  certificateFrom 837959 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4],
  certificateFrom 838311 [1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 2, 3],
  certificateFrom 838887 [1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3],
  certificateFrom 845543 [1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2],
  certificateFrom 853607 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5],
  certificateFrom 854183 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 3, 3],
  certificateFrom 857703 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5],
  certificateFrom 858279 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 3, 3],
  certificateFrom 861799 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3],
  certificateFrom 862375 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 1, 3],
  certificateFrom 864327 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 3, 4],
  certificateFrom 869607 [1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4],
  certificateFrom 872519 [1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 1, 4],
  certificateFrom 872935 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3],
  certificateFrom 874343 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4],
  certificateFrom 877031 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3],
  certificateFrom 880711 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 2, 2],
  certificateFrom 881127 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3],
  certificateFrom 882535 [1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4],
  certificateFrom 884807 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 2],
  certificateFrom 889511 [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2],
  certificateFrom 889959 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3],
  certificateFrom 890727 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2],
  certificateFrom 892999 [1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2],
  certificateFrom 895207 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5]]

private theorem checked07 : ∀ c ∈ cs07, Accepted c := by
  decide +kernel

private def cs08 : List Certificate :=
[  certificateFrom 902247 [1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3],
  certificateFrom 902983 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2],
  certificateFrom 905383 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 4, 2],
  certificateFrom 910407 [1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 2, 3],
  certificateFrom 911175 [1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2],
  certificateFrom 913575 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 2, 2],
  certificateFrom 914759 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4],
  certificateFrom 914791 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4],
  certificateFrom 928871 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4],
  certificateFrom 931143 [1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2],
  certificateFrom 931751 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2],
  certificateFrom 932167 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3],
  certificateFrom 932967 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4],
  certificateFrom 936263 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3],
  certificateFrom 937063 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2],
  certificateFrom 939175 [1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 2, 3],
  certificateFrom 939943 [1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2],
  certificateFrom 941159 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2],
  certificateFrom 945255 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2],
  certificateFrom 952679 [1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3],
  certificateFrom 971431 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 3, 3],
  certificateFrom 978663 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2],
  certificateFrom 982183 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 3, 2],
  certificateFrom 983783 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5],
  certificateFrom 987303 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 2, 5],
  certificateFrom 991559 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2],
  certificateFrom 996071 [1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3],
  certificateFrom 1004903 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5],
  certificateFrom 1006247 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 3, 4],
  certificateFrom 1007975 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2],
  certificateFrom 1008999 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5],
  certificateFrom 1013095 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3],
  certificateFrom 1014439 [1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 1, 4],
  certificateFrom 1015399 [1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3],
  certificateFrom 1016167 [1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2],
  certificateFrom 1018983 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7],
  certificateFrom 1021863 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3],
  certificateFrom 1022055 [1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2],
  certificateFrom 1022631 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 2, 2],
  certificateFrom 1026727 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 2, 2],
  certificateFrom 1034151 [1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3],
  certificateFrom 1034407 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 6],
  certificateFrom 1034919 [1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2],
  certificateFrom 1039079 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2],
  certificateFrom 1041255 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3],
  certificateFrom 1050215 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2],
  certificateFrom 1052327 [1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 2, 3],
  certificateFrom 1053159 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6],
  certificateFrom 1053543 [1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3],
  certificateFrom 1054311 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2]]

private theorem checked08 : ∀ c ∈ cs08, Accepted c := by
  decide +kernel

private def cs09 : List Certificate :=
[  certificateFrom 1058407 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2],
  certificateFrom 1064295 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2],
  certificateFrom 1072295 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3],
  certificateFrom 1076391 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3],
  certificateFrom 1077159 [1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 1, 4],
  certificateFrom 1081671 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3],
  certificateFrom 1084583 [1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3],
  certificateFrom 1085767 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3],
  certificateFrom 1090631 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 1, 4],
  certificateFrom 1091815 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2],
  certificateFrom 1093959 [1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3],
  certificateFrom 1096551 [1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4],
  certificateFrom 1098823 [1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 1, 4],
  certificateFrom 1099879 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3],
  certificateFrom 1103591 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4],
  certificateFrom 1103975 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3],
  certificateFrom 1105767 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5],
  certificateFrom 1107015 [1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 2, 2],
  certificateFrom 1108071 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3],
  certificateFrom 1109223 [1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3],
  certificateFrom 1116487 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4],
  certificateFrom 1119399 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 1, 4],
  certificateFrom 1124679 [1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4],
  certificateFrom 1124711 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4],
  certificateFrom 1125095 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3],
  certificateFrom 1127591 [1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 1, 4],
  certificateFrom 1128807 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4],
  certificateFrom 1132135 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5],
  certificateFrom 1132711 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 4, 3],
  certificateFrom 1132871 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2],
  certificateFrom 1133287 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3],
  certificateFrom 1135783 [1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2],
  certificateFrom 1140903 [1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 2, 3],
  certificateFrom 1150279 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5],
  certificateFrom 1151463 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3],
  certificateFrom 1152231 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2],
  certificateFrom 1154407 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3],
  certificateFrom 1158055 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 3, 2],
  certificateFrom 1159655 [1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3],
  certificateFrom 1163335 [1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2],
  certificateFrom 1165159 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2],
  certificateFrom 1166247 [1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 3, 2],
  certificateFrom 1171623 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 2, 6],
  certificateFrom 1172199 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4],
  certificateFrom 1176295 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4],
  certificateFrom 1180391 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2],
  certificateFrom 1183911 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 5, 2],
  certificateFrom 1184487 [1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4],
  certificateFrom 1192103 [1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 3, 2],
  certificateFrom 1192679 [1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2]]

private theorem checked09 : ∀ c ∈ cs09, Accepted c := by
  decide +kernel

private def cs10 : List Certificate :=
[  certificateFrom 1193703 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5],
  certificateFrom 1197799 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5],
  certificateFrom 1198919 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3],
  certificateFrom 1201479 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2],
  certificateFrom 1201511 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2],
  certificateFrom 1201895 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3],
  certificateFrom 1205575 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2],
  certificateFrom 1205607 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2],
  certificateFrom 1207111 [1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3],
  certificateFrom 1209703 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2],
  certificateFrom 1213767 [1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2],
  certificateFrom 1214951 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2],
  certificateFrom 1221479 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6],
  certificateFrom 1223015 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3],
  certificateFrom 1223143 [1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2],
  certificateFrom 1225575 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4],
  certificateFrom 1227111 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3],
  certificateFrom 1232551 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 1, 4],
  certificateFrom 1235303 [1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3],
  certificateFrom 1237831 [1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4],
  certificateFrom 1240743 [1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 1, 4],
  certificateFrom 1241159 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 3, 3],
  certificateFrom 1242343 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3],
  certificateFrom 1245255 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 3],
  certificateFrom 1246439 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3],
  certificateFrom 1248935 [1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 2, 2],
  certificateFrom 1249351 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 1, 3],
  certificateFrom 1251175 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3],
  certificateFrom 1254631 [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3],
  certificateFrom 1259367 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3],
  certificateFrom 1263431 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5],
  certificateFrom 1269927 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 5, 3],
  certificateFrom 1274023 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 3, 3],
  certificateFrom 1278119 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 1, 3],
  certificateFrom 1279463 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4],
  certificateFrom 1280103 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6],
  certificateFrom 1283431 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5],
  certificateFrom 1286503 [1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2],
  certificateFrom 1289447 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4],
  certificateFrom 1297639 [1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4],
  certificateFrom 1302375 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2],
  certificateFrom 1305255 [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 3, 2],
  certificateFrom 1305319 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6],
  certificateFrom 1305703 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3],
  certificateFrom 1305831 [1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2],
  certificateFrom 1317991 [1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3],
  certificateFrom 1319783 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3],
  certificateFrom 1321127 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 1, 4],
  certificateFrom 1323879 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3],
  certificateFrom 1328743 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2]]

private theorem checked10 : ∀ c ∈ cs10, Accepted c := by
  decide +kernel

private def cs11 : List Certificate :=
[  certificateFrom 1330535 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4],
  certificateFrom 1336935 [1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2],
  certificateFrom 1337511 [1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2],
  certificateFrom 1339879 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4],
  certificateFrom 1342631 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 5],
  certificateFrom 1346887 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2],
  certificateFrom 1352007 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5],
  certificateFrom 1354919 [1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 2, 3],
  certificateFrom 1355495 [1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3],
  certificateFrom 1356263 [1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2],
  certificateFrom 1360999 [1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4],
  certificateFrom 1364295 [1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3],
  certificateFrom 1368423 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3],
  certificateFrom 1377767 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3],
  certificateFrom 1378407 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3],
  certificateFrom 1379175 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2],
  certificateFrom 1383079 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 3, 3],
  certificateFrom 1384295 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5],
  certificateFrom 1385959 [1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3],
  certificateFrom 1386599 [1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3],
  certificateFrom 1387175 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 3, 3],
  certificateFrom 1390311 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2],
  certificateFrom 1391271 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 1, 3],
  certificateFrom 1394407 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2],
  certificateFrom 1398503 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2],
  certificateFrom 1399527 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5],
  certificateFrom 1403239 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4],
  certificateFrom 1403623 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3],
  certificateFrom 1407303 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2],
  certificateFrom 1411431 [1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4],
  certificateFrom 1411815 [1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3],
  certificateFrom 1418855 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3],
  certificateFrom 1419623 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2],
  certificateFrom 1420647 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5],
  certificateFrom 1421383 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 1, 6],
  certificateFrom 1423719 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2],
  certificateFrom 1424743 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5],
  certificateFrom 1428839 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3],
  certificateFrom 1431143 [1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3],
  certificateFrom 1431399 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6],
  certificateFrom 1431911 [1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2],
  certificateFrom 1441895 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2],
  certificateFrom 1450087 [1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2],
  certificateFrom 1453991 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3],
  certificateFrom 1460039 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2],
  certificateFrom 1462183 [1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 3],
  certificateFrom 1468647 [1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3],
  certificateFrom 1469287 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3],
  certificateFrom 1471815 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4],
  certificateFrom 1472231 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5]]

private theorem checked11 : ∀ c ∈ cs11, Accepted c := by
  decide +kernel

private def cs12 : List Certificate :=
[  certificateFrom 1473383 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3],
  certificateFrom 1474151 [1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4],
  certificateFrom 1477447 [1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3],
  certificateFrom 1480039 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2],
  certificateFrom 1481575 [1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3],
  certificateFrom 1485927 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6],
  certificateFrom 1488231 [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2],
  certificateFrom 1490023 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4],
  certificateFrom 1492903 [1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4],
  certificateFrom 1493319 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3],
  certificateFrom 1501511 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3],
  certificateFrom 1504103 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4],
  certificateFrom 1512295 [1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4],
  certificateFrom 1512679 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5],
  certificateFrom 1518503 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 1, 5],
  certificateFrom 1519687 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 4, 3],
  certificateFrom 1520455 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2],
  certificateFrom 1520487 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2],
  certificateFrom 1524967 [1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3],
  certificateFrom 1525607 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5],
  certificateFrom 1527879 [1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 2, 3],
  certificateFrom 1529703 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3],
  certificateFrom 1531047 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 4],
  certificateFrom 1535143 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 1, 4],
  certificateFrom 1537895 [1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3],
  certificateFrom 1539239 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2],
  certificateFrom 1540423 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4],
  certificateFrom 1543335 [1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 1, 4],
  certificateFrom 1544519 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4],
  certificateFrom 1548615 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2],
  certificateFrom 1551527 [1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2],
  certificateFrom 1552711 [1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4],
  certificateFrom 1555047 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2],
  certificateFrom 1557223 [1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3],
  certificateFrom 1560903 [1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2],
  certificateFrom 1561927 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5],
  certificateFrom 1563239 [1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2],
  certificateFrom 1563303 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 1, 6],
  certificateFrom 1566023 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5],
  certificateFrom 1566823 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4],
  certificateFrom 1568615 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8],
  certificateFrom 1570119 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3],
  certificateFrom 1570151 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3],
  certificateFrom 1574375 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2],
  certificateFrom 1575399 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5],
  certificateFrom 1580903 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2],
  certificateFrom 1582439 [1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3],
  certificateFrom 1582567 [1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2],
  certificateFrom 1583175 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 3, 2],
  certificateFrom 1583207 [1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2]]

private theorem checked12 : ∀ c ∈ cs12, Accepted c := by
  decide +kernel

private def cs13 : List Certificate :=
[  certificateFrom 1584231 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3],
  certificateFrom 1588327 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3],
  certificateFrom 1591367 [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 3, 2],
  certificateFrom 1592039 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4],
  certificateFrom 1596135 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2],
  certificateFrom 1607847 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 3, 2],
  certificateFrom 1608423 [1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2],
  certificateFrom 1609063 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4],
  certificateFrom 1610567 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3],
  certificateFrom 1611943 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 3, 2],
  certificateFrom 1613159 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4],
  certificateFrom 1614663 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3],
  certificateFrom 1617255 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2],
  certificateFrom 1620135 [1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 3, 2],
  certificateFrom 1621351 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2],
  certificateFrom 1622855 [1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3],
  certificateFrom 1625447 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2],
  certificateFrom 1626599 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2],
  certificateFrom 1630695 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2],
  certificateFrom 1638887 [1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2],
  certificateFrom 1643623 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2],
  certificateFrom 1647687 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 2, 4],
  certificateFrom 1657671 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4],
  certificateFrom 1661607 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 4, 3],
  certificateFrom 1665863 [1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4],
  certificateFrom 1668839 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2],
  certificateFrom 1669799 [1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 2, 3],
  certificateFrom 1673543 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6],
  certificateFrom 1674055 [1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2],
  certificateFrom 1676455 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 2, 4],
  certificateFrom 1677031 [1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2],
  certificateFrom 1678055 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5],
  certificateFrom 1699175 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7],
  certificateFrom 1701095 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4],
  certificateFrom 1702247 [1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2],
  certificateFrom 1705191 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4],
  certificateFrom 1708103 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 4],
  certificateFrom 1709287 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2],
  certificateFrom 1713383 [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4],
  certificateFrom 1715111 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 4, 2],
  certificateFrom 1718119 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4],
  certificateFrom 1721575 [1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2],
  certificateFrom 1722215 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2],
  certificateFrom 1723719 [1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3],
  certificateFrom 1724487 [1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2],
  certificateFrom 1725095 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 3, 2],
  certificateFrom 1729255 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4],
  certificateFrom 1732519 [1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 3],
  certificateFrom 1733287 [1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 3, 2],
  certificateFrom 1733351 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4]]

private theorem checked13 : ∀ c ∈ cs13, Accepted c := by
  decide +kernel

private def cs14 : List Certificate :=
[  certificateFrom 1733735 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3],
  certificateFrom 1734503 [1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2],
  certificateFrom 1736871 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 1, 4],
  certificateFrom 1737831 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3],
  certificateFrom 1739623 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5],
  certificateFrom 1745991 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 2, 3],
  certificateFrom 1746023 [1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3],
  certificateFrom 1751911 [1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3],
  certificateFrom 1754183 [1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 2, 3],
  certificateFrom 1758535 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2],
  certificateFrom 1758951 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3],
  certificateFrom 1762631 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2],
  certificateFrom 1766727 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2],
  certificateFrom 1767751 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5],
  certificateFrom 1768551 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4],
  certificateFrom 1771239 [1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3],
  certificateFrom 1771847 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3],
  certificateFrom 1772007 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2],
  certificateFrom 1774759 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 2, 3],
  certificateFrom 1775527 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2],
  certificateFrom 1776743 [1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4],
  certificateFrom 1780039 [1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3],
  certificateFrom 1780071 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3],
  certificateFrom 1782951 [1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 2, 3],
  certificateFrom 1784167 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3],
  certificateFrom 1784935 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2],
  certificateFrom 1788263 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3],
  certificateFrom 1789607 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 2, 4],
  certificateFrom 1794919 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2],
  certificateFrom 1802343 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5],
  certificateFrom 1804135 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5],
  certificateFrom 1814247 [1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4],
  certificateFrom 1827559 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3],
  certificateFrom 1831655 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3],
  certificateFrom 1836871 [1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3],
  certificateFrom 1839847 [1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3],
  certificateFrom 1840455 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5],
  certificateFrom 1846503 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4],
  certificateFrom 1850023 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 1, 4],
  certificateFrom 1850983 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3],
  certificateFrom 1851239 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4],
  certificateFrom 1852903 [1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2],
  certificateFrom 1853543 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2],
  certificateFrom 1857639 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2],
  certificateFrom 1859175 [1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3],
  certificateFrom 1865639 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3],
  certificateFrom 1865831 [1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2],
  certificateFrom 1866407 [1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 2, 2],
  certificateFrom 1869735 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3],
  certificateFrom 1874663 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2]]

private theorem checked14 : ∀ c ∈ cs14, Accepted c := by
  decide +kernel

private def cs15 : List Certificate :=
[  certificateFrom 1877927 [1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3],
  certificateFrom 1878183 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 2, 4],
  certificateFrom 1878759 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2],
  certificateFrom 1880903 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5],
  certificateFrom 1880935 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3],
  certificateFrom 1887911 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 2, 3],
  certificateFrom 1889127 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3],
  certificateFrom 1889895 [1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4],
  certificateFrom 1893191 [1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3],
  certificateFrom 1896103 [1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 2, 3],
  certificateFrom 1896935 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4],
  certificateFrom 1912743 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4],
  certificateFrom 1915495 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5],
  certificateFrom 1916071 [1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3],
  certificateFrom 1920935 [1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 1, 4],
  certificateFrom 1925447 [1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3],
  certificateFrom 1927399 [1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4],
  certificateFrom 1928039 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4],
  certificateFrom 1929127 [1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2],
  certificateFrom 1932135 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4],
  certificateFrom 1934823 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3],
  certificateFrom 1936231 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2],
  certificateFrom 1940327 [1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4],
  certificateFrom 1942599 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 2, 2],
  certificateFrom 1943623 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 1, 5],
  certificateFrom 1944807 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3],
  certificateFrom 1948519 [1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2],
  certificateFrom 1950791 [1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2],
  certificateFrom 1952999 [1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3],
  certificateFrom 1960263 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4],
  certificateFrom 1960295 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6],
  certificateFrom 1964359 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2],
  certificateFrom 1968295 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 1, 5],
  certificateFrom 1971367 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2],
  certificateFrom 1972391 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 1, 5],
  certificateFrom 1976487 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 2, 3],
  certificateFrom 1976647 [1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2],
  certificateFrom 1979559 [1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 2, 2],
  certificateFrom 1985895 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3],
  certificateFrom 1987047 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5],
  certificateFrom 1991143 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5],
  certificateFrom 1994823 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 3, 2],
  certificateFrom 1995239 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3],
  certificateFrom 1998183 [1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3],
  certificateFrom 1998919 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 2],
  certificateFrom 1998951 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2],
  certificateFrom 2000743 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2],
  certificateFrom 2004071 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5],
  certificateFrom 2004839 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2],
  certificateFrom 2007111 [1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2]]

private theorem checked15 : ∀ c ∈ cs15, Accepted c := by
  decide +kernel

private def cs16 : List Certificate :=
[  certificateFrom 2007783 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4],
  certificateFrom 2015975 [1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4],
  certificateFrom 2016359 [1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3],
  certificateFrom 2024167 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2],
  certificateFrom 2027687 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 3, 2],
  certificateFrom 2028263 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2],
  certificateFrom 2036455 [1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2],
  certificateFrom 2037063 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2],
  certificateFrom 2041191 [1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4],
  certificateFrom 2045255 [1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2],
  certificateFrom 2046279 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5],
  certificateFrom 2058599 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3],
  certificateFrom 2059367 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2],
  certificateFrom 2061159 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6],
  certificateFrom 2066791 [1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3],
  certificateFrom 2069319 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4],
  certificateFrom 2073415 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4],
  certificateFrom 2077511 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2],
  certificateFrom 2081607 [1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4],
  certificateFrom 2084519 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 2, 2],
  certificateFrom 2085543 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 1, 5],
  certificateFrom 2086119 [1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3],
  certificateFrom 2088103 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 2, 4],
  certificateFrom 2089799 [1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2],
  certificateFrom 2091943 [1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 1, 3],
  certificateFrom 2092199 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 2, 4],
  certificateFrom 2092711 [1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 2, 2],
  certificateFrom 2097479 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4],
  certificateFrom 2101575 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4],
  certificateFrom 2112103 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2],
  certificateFrom 2117799 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 1, 3],
  certificateFrom 2122087 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2],
  certificateFrom 2123879 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4],
  certificateFrom 2127175 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3],
  certificateFrom 2129511 [1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3],
  certificateFrom 2130279 [1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2],
  certificateFrom 2135975 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5],
  certificateFrom 2136743 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 3, 2],
  certificateFrom 2139463 [1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3],
  certificateFrom 2140231 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 4, 2],
  certificateFrom 2140839 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2],
  certificateFrom 2141415 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2],
  certificateFrom 2144999 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4],
  certificateFrom 2145383 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3],
  certificateFrom 2148263 [1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3],
  certificateFrom 2148839 [1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3],
  certificateFrom 2149031 [1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 3, 2],
  certificateFrom 2149095 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4],
  certificateFrom 2149607 [1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2],
  certificateFrom 2153575 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3]]

private theorem checked16 : ∀ c ∈ cs16, Accepted c := by
  decide +kernel

private def cs17 : List Certificate :=
[  certificateFrom 2155367 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5],
  certificateFrom 2159463 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3],
  certificateFrom 2164903 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 4, 2],
  certificateFrom 2166119 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6],
  certificateFrom 2167655 [1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3],
  certificateFrom 2168999 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 4, 2],
  certificateFrom 2170215 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4],
  certificateFrom 2172519 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2],
  certificateFrom 2173095 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2],
  certificateFrom 2182471 [1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4],
  certificateFrom 2183655 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2],
  certificateFrom 2186407 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 2, 3],
  certificateFrom 2187751 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2],
  certificateFrom 2190503 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 2, 3],
  certificateFrom 2191079 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3],
  certificateFrom 2191847 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2],
  certificateFrom 2192487 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4],
  certificateFrom 2195783 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3],
  certificateFrom 2196583 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4],
  certificateFrom 2198695 [1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 2, 3],
  certificateFrom 2199271 [1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3],
  certificateFrom 2199879 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3],
  certificateFrom 2200679 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2],
  certificateFrom 2204775 [1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4],
  certificateFrom 2208071 [1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3],
  certificateFrom 2212967 [1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2],
  certificateFrom 2213991 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5],
  certificateFrom 2214727 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4],
  certificateFrom 2218087 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5],
  certificateFrom 2221127 [1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 3, 2],
  certificateFrom 2222183 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3],
  certificateFrom 2229991 [1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4],
  certificateFrom 2239207 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5],
  certificateFrom 2242887 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2],
  certificateFrom 2246823 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 2, 5],
  certificateFrom 2246983 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2],
  certificateFrom 2247015 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4],
  certificateFrom 2247399 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3],
  certificateFrom 2249895 [1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 3, 2],
  certificateFrom 2258151 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4],
  certificateFrom 2262247 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4],
  certificateFrom 2262631 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3],
  certificateFrom 2263399 [1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2],
  certificateFrom 2264423 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3],
  certificateFrom 2265159 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 2, 4],
  certificateFrom 2265575 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5],
  certificateFrom 2266727 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3],
  certificateFrom 2268519 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3],
  certificateFrom 2271079 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4],
  certificateFrom 2274919 [1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3]]

private theorem checked17 : ∀ c ∈ cs17, Accepted c := by
  decide +kernel

private def cs18 : List Certificate :=
[  certificateFrom 2275175 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4],
  certificateFrom 2282151 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 4, 2],
  certificateFrom 2293927 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 2, 4],
  certificateFrom 2295623 [1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4],
  certificateFrom 2303047 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 3, 3],
  certificateFrom 2304231 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3],
  certificateFrom 2306791 [1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2],
  certificateFrom 2309735 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4],
  certificateFrom 2312423 [1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3],
  certificateFrom 2313031 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3],
  certificateFrom 2313063 [1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3],
  certificateFrom 2317927 [1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4],
  certificateFrom 2321223 [1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3],
  certificateFrom 2323815 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2],
  certificateFrom 2324391 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4],
  certificateFrom 2325607 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6],
  certificateFrom 2326119 [1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2],
  certificateFrom 2328487 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4],
  certificateFrom 2331815 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 3, 3],
  certificateFrom 2332583 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2],
  certificateFrom 2336679 [1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4],
  certificateFrom 2344871 [1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2],
  certificateFrom 2347879 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4],
  certificateFrom 2351975 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2],
  certificateFrom 2355271 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 1, 5],
  certificateFrom 2356455 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3],
  certificateFrom 2359367 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 5],
  certificateFrom 2360551 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3],
  certificateFrom 2363047 [1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 3, 2],
  certificateFrom 2363463 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 2, 3],
  certificateFrom 2364263 [1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2],
  certificateFrom 2365287 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5],
  certificateFrom 2366631 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 4],
  certificateFrom 2368743 [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3],
  certificateFrom 2373479 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3],
  certificateFrom 2374823 [1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 1, 4],
  certificateFrom 2375783 [1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3],
  certificateFrom 2376007 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4],
  certificateFrom 2383015 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2],
  certificateFrom 2384039 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 3, 5],
  certificateFrom 2384199 [1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4],
  certificateFrom 2384615 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3],
  certificateFrom 2387111 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2],
  certificateFrom 2388135 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 1, 5],
  certificateFrom 2388711 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3],
  certificateFrom 2392231 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 2, 3],
  certificateFrom 2392391 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2],
  certificateFrom 2392807 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3],
  certificateFrom 2395303 [1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 2, 2],
  certificateFrom 2396487 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2]]

private theorem checked18 : ∀ c ∈ cs18, Accepted c := by
  decide +kernel

private def cs19 : List Certificate :=
[  certificateFrom 2404679 [1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2],
  certificateFrom 2407079 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 4],
  certificateFrom 2408295 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6],
  certificateFrom 2410599 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2],
  certificateFrom 2413927 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3],
  certificateFrom 2414695 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2],
  certificateFrom 2418023 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3],
  certificateFrom 2418791 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2],
  certificateFrom 2419815 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5],
  certificateFrom 2419943 [1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2],
  certificateFrom 2423911 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3],
  certificateFrom 2426215 [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3],
  certificateFrom 2432103 [1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3],
  certificateFrom 2433895 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5],
  certificateFrom 2435815 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2],
  certificateFrom 2443431 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 5, 2],
  certificateFrom 2444007 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2],
  certificateFrom 2444967 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 3, 3],
  certificateFrom 2448743 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4],
  certificateFrom 2451623 [1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 3, 2],
  certificateFrom 2454343 [1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3],
  certificateFrom 2456935 [1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4],
  certificateFrom 2462183 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2],
  certificateFrom 2465127 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2],
  certificateFrom 2469607 [1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3],
  certificateFrom 2469799 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4],
  certificateFrom 2470375 [1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2],
  certificateFrom 2482535 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5],
  certificateFrom 2485095 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4],
  certificateFrom 2488935 [1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3],
  certificateFrom 2489191 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4],
  certificateFrom 2492519 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5],
  certificateFrom 2497191 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 1, 5],
  certificateFrom 2501287 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 1, 5],
  certificateFrom 2501863 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3],
  certificateFrom 2505383 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 2, 3],
  certificateFrom 2506599 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3],
  certificateFrom 2509639 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2],
  certificateFrom 2512615 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2],
  certificateFrom 2513223 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4],
  certificateFrom 2514791 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3],
  certificateFrom 2517063 [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 3],
  certificateFrom 2517319 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4],
  certificateFrom 2517735 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5],
  certificateFrom 2517831 [1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2],
  certificateFrom 2532967 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5],
  certificateFrom 2533543 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 3, 3],
  certificateFrom 2533735 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2],
  certificateFrom 2536679 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4],
  certificateFrom 2537831 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2]]

private theorem checked19 : ∀ c ∈ cs19, Accepted c := by
  decide +kernel

private def cs20 : List Certificate :=
[  certificateFrom 2544871 [1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4],
  certificateFrom 2545255 [1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3],
  certificateFrom 2545831 [1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3],
  certificateFrom 2546023 [1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2],
  certificateFrom 2550695 [1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 1, 4],
  certificateFrom 2551879 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 4, 2],
  certificateFrom 2552295 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3],
  certificateFrom 2553063 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2],
  certificateFrom 2555975 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4, 2],
  certificateFrom 2557159 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2],
  certificateFrom 2559303 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3],
  certificateFrom 2560071 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 2],
  certificateFrom 2561895 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2],
  certificateFrom 2564583 [1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3],
  certificateFrom 2564839 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6],
  certificateFrom 2565351 [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2],
  certificateFrom 2567495 [1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3],
  certificateFrom 2568103 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3],
  certificateFrom 2570087 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2],
  certificateFrom 2572455 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 3, 4],
  certificateFrom 2576295 [1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 2, 3],
  certificateFrom 2576551 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 1, 4],
  certificateFrom 2577511 [1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3],
  certificateFrom 2580647 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 6, 2],
  certificateFrom 2582759 [1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3],
  certificateFrom 2583399 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3],
  certificateFrom 2584743 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 4, 2],
  certificateFrom 2587495 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3],
  certificateFrom 2588839 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 2, 2],
  certificateFrom 2595687 [1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3],
  certificateFrom 2598215 [1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4],
  certificateFrom 2602727 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3],
  certificateFrom 2606823 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3],
  certificateFrom 2607431 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5],
  certificateFrom 2607591 [1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4],
  certificateFrom 2612327 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4],
  certificateFrom 2615015 [1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3],
  certificateFrom 2615623 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3],
  certificateFrom 2616423 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2],
  certificateFrom 2626375 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4],
  certificateFrom 2628711 [1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2],
  certificateFrom 2630471 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4],
  certificateFrom 2630503 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2],
  certificateFrom 2633799 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 2, 5],
  certificateFrom 2634599 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2],
  certificateFrom 2643815 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5],
  certificateFrom 2649831 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4],
  certificateFrom 2658023 [1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4],
  certificateFrom 2658983 [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 3],
  certificateFrom 2662567 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 7]]

private theorem checked20 : ∀ c ∈ cs20, Accepted c := by
  decide +kernel

private def cs21 : List Certificate :=
[  certificateFrom 2663143 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3],
  certificateFrom 2665639 [1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 3, 2],
  certificateFrom 2666215 [1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2],
  certificateFrom 2671335 [1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3],
  certificateFrom 2672455 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3],
  certificateFrom 2675015 [1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2],
  certificateFrom 2679143 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2],
  certificateFrom 2680647 [1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3],
  certificateFrom 2684263 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5],
  certificateFrom 2688487 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2],
  certificateFrom 2689127 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2],
  certificateFrom 2693799 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2],
  certificateFrom 2696551 [1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3],
  certificateFrom 2696679 [1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2],
  certificateFrom 2697319 [1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2],
  certificateFrom 2697895 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 4, 2],
  certificateFrom 2698343 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5],
  certificateFrom 2701991 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 2, 2],
  certificateFrom 2702055 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6],
  certificateFrom 2709415 [1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3],
  certificateFrom 2714343 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2],
  certificateFrom 2721383 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4],
  certificateFrom 2722535 [1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2],
  certificateFrom 2724679 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3],
  certificateFrom 2725479 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4],
  certificateFrom 2728775 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3],
  certificateFrom 2729575 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2],
  certificateFrom 2733671 [1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4],
  certificateFrom 2736967 [1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3],
  certificateFrom 2739559 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2],
  certificateFrom 2741863 [1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2],
  certificateFrom 2743463 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 3, 3],
  certificateFrom 2747559 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 3, 3],
  certificateFrom 2749543 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4],
  certificateFrom 2751655 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 3],
  certificateFrom 2752839 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3],
  certificateFrom 2753639 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4],
  certificateFrom 2756935 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3],
  certificateFrom 2761031 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3],
  certificateFrom 2762983 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4],
  certificateFrom 2763623 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4],
  certificateFrom 2764711 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2],
  certificateFrom 2771175 [1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4],
  certificateFrom 2771815 [1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4],
  certificateFrom 2772903 [1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2],
  certificateFrom 2775719 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 2, 5],
  certificateFrom 2779239 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3],
  certificateFrom 2779367 [1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2],
  certificateFrom 2780007 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2],
  certificateFrom 2784103 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2]]

private theorem checked21 : ∀ c ∈ cs21, Accepted c := by
  decide +kernel

private def cs22 : List Certificate :=
[  certificateFrom 2788167 [1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2],
  certificateFrom 2791527 [1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3],
  certificateFrom 2792295 [1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2],
  certificateFrom 2800359 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3],
  certificateFrom 2804039 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2],
  certificateFrom 2804071 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4],
  certificateFrom 2804455 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3],
  certificateFrom 2808551 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3],
  certificateFrom 2812231 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2],
  certificateFrom 2825575 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3],
  certificateFrom 2828135 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6],
  certificateFrom 2830407 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 5, 2],
  certificateFrom 2833767 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3],
  certificateFrom 2834535 [1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4],
  certificateFrom 2835687 [1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2],
  certificateFrom 2837831 [1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3],
  certificateFrom 2838599 [1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3, 2],
  certificateFrom 2840423 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2],
  certificateFrom 2847847 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3],
  certificateFrom 2848615 [1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2],
  certificateFrom 2851559 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4],
  certificateFrom 2851943 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3],
  certificateFrom 2860135 [1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3],
  certificateFrom 2866791 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4],
  certificateFrom 2867943 [1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2],
  certificateFrom 2870087 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3],
  certificateFrom 2872679 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4],
  certificateFrom 2873063 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5],
  certificateFrom 2876775 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4],
  certificateFrom 2880839 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2],
  certificateFrom 2880871 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2],
  certificateFrom 2881447 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4],
  certificateFrom 2884967 [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4],
  certificateFrom 2885351 [1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3],
  certificateFrom 2885543 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4],
  certificateFrom 2885959 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5],
  certificateFrom 2893159 [1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2],
  certificateFrom 2894183 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5],
  certificateFrom 2894951 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2],
  certificateFrom 2898279 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5],
  certificateFrom 2899047 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2],
  certificateFrom 2900839 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4],
  certificateFrom 2902375 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3],
  certificateFrom 2904903 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4],
  certificateFrom 2904935 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4],
  certificateFrom 2913095 [1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4],
  certificateFrom 2913511 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3],
  certificateFrom 2917607 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3],
  certificateFrom 2920519 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 3, 3],
  certificateFrom 2921287 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2]]

private theorem checked22 : ∀ c ∈ cs22, Accepted c := by
  decide +kernel

private def cs23 : List Certificate :=
[  certificateFrom 2921703 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3],
  certificateFrom 2923687 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 6],
  certificateFrom 2925383 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2],
  certificateFrom 2926439 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3],
  certificateFrom 2927527 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 1, 3],
  certificateFrom 2930535 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3],
  certificateFrom 2932807 [1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 1, 3],
  certificateFrom 2933063 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6],
  certificateFrom 2933575 [1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2],
  certificateFrom 2934631 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3],
  certificateFrom 2935719 [1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3],
  certificateFrom 2947687 [1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4],
  certificateFrom 2949287 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 3, 3],
  certificateFrom 2950983 [1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3],
  certificateFrom 2961575 [1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 1, 3],
  certificateFrom 2965095 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3],
  certificateFrom 2969447 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4],
  certificateFrom 2970951 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3],
  certificateFrom 2972327 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 5, 2],
  certificateFrom 2973287 [1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3],
  certificateFrom 2973543 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4],
  certificateFrom 2975047 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3],
  certificateFrom 2975815 [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 1, 4],
  certificateFrom 2979751 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3],
  certificateFrom 2980519 [1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 3, 2],
  certificateFrom 2983239 [1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3],
  certificateFrom 2983847 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3],
  certificateFrom 2984423 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3],
  certificateFrom 2992039 [1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3],
  certificateFrom 2992615 [1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3],
  certificateFrom 2995047 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5],
  certificateFrom 3003239 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3],
  certificateFrom 3004583 [1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 1, 4],
  certificateFrom 3005799 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6],
  certificateFrom 3018055 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4],
  certificateFrom 3021991 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 4, 3],
  certificateFrom 3023335 [1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4],
  certificateFrom 3026247 [1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4],
  certificateFrom 3028071 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4],
  certificateFrom 3030183 [1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 2, 3],
  certificateFrom 3031367 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3],
  certificateFrom 3034439 [1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2],
  certificateFrom 3036263 [1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4],
  certificateFrom 3039559 [1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3],
  certificateFrom 3043239 [1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 3, 2],
  certificateFrom 3044455 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2],
  certificateFrom 3048551 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2],
  certificateFrom 3048935 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5],
  certificateFrom 3055975 [1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3],
  certificateFrom 3056711 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 3, 2]]

private theorem checked23 : ∀ c ∈ cs23, Accepted c := by
  decide +kernel

private def cs24 : List Certificate :=
[  certificateFrom 3056743 [1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2],
  certificateFrom 3061479 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4],
  certificateFrom 3062439 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 3, 3],
  certificateFrom 3062631 [1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2],
  certificateFrom 3064903 [1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 3, 2],
  certificateFrom 3065575 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4],
  certificateFrom 3069671 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2],
  certificateFrom 3070279 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6],
  certificateFrom 3073767 [1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4],
  certificateFrom 3074727 [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 3],
  certificateFrom 3081959 [1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2],
  certificateFrom 3082567 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2],
  certificateFrom 3085479 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 3, 2],
  certificateFrom 3090759 [1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2],
  certificateFrom 3090791 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2],
  certificateFrom 3093671 [1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 3, 2],
  certificateFrom 3093735 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6],
  certificateFrom 3094887 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2],
  certificateFrom 3098983 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2],
  certificateFrom 3100007 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5],
  certificateFrom 3104103 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3],
  certificateFrom 3106407 [1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3],
  certificateFrom 3112295 [1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3],
  certificateFrom 3117735 [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 1, 4],
  certificateFrom 3125159 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3],
  certificateFrom 3129511 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 1, 6],
  certificateFrom 3131207 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4],
  certificateFrom 3133607 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 2, 4],
  certificateFrom 3138279 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2],
  certificateFrom 3139399 [1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4],
  certificateFrom 3140455 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3],
  certificateFrom 3142375 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2],
  certificateFrom 3144551 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3],
  certificateFrom 3147591 [1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2],
  certificateFrom 3148647 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3],
  certificateFrom 3150567 [1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2],
  certificateFrom 3159975 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4],
  certificateFrom 3161703 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2],
  certificateFrom 3165287 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4],
  certificateFrom 3168167 [1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4],
  certificateFrom 3168583 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3],
  certificateFrom 3169383 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4],
  certificateFrom 3169895 [1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2],
  certificateFrom 3172679 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3],
  certificateFrom 3172711 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5],
  certificateFrom 3176359 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2],
  certificateFrom 3176775 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3],
  certificateFrom 3180455 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2],
  certificateFrom 3188647 [1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2],
  certificateFrom 3191655 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2]]

private theorem checked24 : ∀ c ∈ cs24, Accepted c := by
  decide +kernel

private def cs25 : List Certificate :=
[  certificateFrom 3192039 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3],
  certificateFrom 3198631 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 3, 2],
  certificateFrom 3199847 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2],
  certificateFrom 3200231 [1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3],
  certificateFrom 3203911 [1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2],
  certificateFrom 3206055 [1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 2, 3],
  certificateFrom 3206823 [1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 3, 2],
  certificateFrom 3206887 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4],
  certificateFrom 3210407 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 4],
  certificateFrom 3211367 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3],
  certificateFrom 3219559 [1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3],
  certificateFrom 3219783 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4],
  certificateFrom 3226791 [1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 2, 2],
  certificateFrom 3227815 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 4, 3],
  certificateFrom 3231911 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3],
  certificateFrom 3236167 [1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2],
  certificateFrom 3241287 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5],
  certificateFrom 3245543 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2],
  certificateFrom 3250279 [1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4],
  certificateFrom 3253575 [1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3],
  certificateFrom 3255527 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2],
  certificateFrom 3257703 [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3],
  certificateFrom 3259495 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5],
  certificateFrom 3262951 [1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3],
  certificateFrom 3263719 [1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2],
  certificateFrom 3267303 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4],
  certificateFrom 3267687 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3],
  certificateFrom 3273575 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5],
  certificateFrom 3278439 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4],
  certificateFrom 3281735 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3],
  certificateFrom 3282535 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4],
  certificateFrom 3285831 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3],
  certificateFrom 3287207 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 3, 2],
  certificateFrom 3289927 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3],
  certificateFrom 3292519 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4],
  certificateFrom 3296615 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2],
  certificateFrom 3305191 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3],
  certificateFrom 3305959 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2],
  certificateFrom 3308903 [1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2],
  certificateFrom 3313383 [1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3],
  certificateFrom 3320039 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4],
  certificateFrom 3320679 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6],
  certificateFrom 3324519 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3],
  certificateFrom 3327079 [1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2],
  certificateFrom 3332711 [1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3],
  certificateFrom 3352647 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 1, 3],
  certificateFrom 3360839 [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 3],
  certificateFrom 3369319 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2],
  certificateFrom 3376743 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3],
  certificateFrom 3377319 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 1, 3]]

private theorem checked25 : ∀ c ∈ cs25, Accepted c := by
  decide +kernel

private def cs26 : List Certificate :=
[  certificateFrom 3377511 [1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2],
  certificateFrom 3378535 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5],
  certificateFrom 3380455 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4],
  certificateFrom 3380839 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3],
  certificateFrom 3381415 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3],
  certificateFrom 3386279 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 1, 4],
  certificateFrom 3389031 [1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3],
  certificateFrom 3389607 [1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 1, 3],
  certificateFrom 3391559 [1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 1, 4],
  certificateFrom 3393383 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4],
  certificateFrom 3394471 [1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4],
  certificateFrom 3396071 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3],
  certificateFrom 3396839 [1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2],
  certificateFrom 3400167 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3],
  certificateFrom 3402663 [1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2],
  certificateFrom 3404903 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3],
  certificateFrom 3408359 [1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3],
  certificateFrom 3408615 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4],
  certificateFrom 3408999 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3],
  certificateFrom 3412135 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 3, 4],
  certificateFrom 3413095 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3],
  certificateFrom 3417159 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 1, 5],
  certificateFrom 3418343 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3],
  certificateFrom 3418983 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3],
  certificateFrom 3420327 [1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 1, 4],
  certificateFrom 3426535 [1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3],
  certificateFrom 3427175 [1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3],
  certificateFrom 3428519 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 2, 2],
  certificateFrom 3429703 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4],
  certificateFrom 3429735 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4],
  certificateFrom 3433799 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4],
  certificateFrom 3433831 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4],
  certificateFrom 3437895 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2],
  certificateFrom 3440231 [1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2],
  certificateFrom 3441991 [1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4],
  certificateFrom 3443175 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4],
  certificateFrom 3445927 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 1, 5],
  certificateFrom 3446503 [1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3],
  certificateFrom 3450183 [1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2],
  certificateFrom 3451367 [1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4],
  certificateFrom 3456103 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2],
  certificateFrom 3457895 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6],
  certificateFrom 3458983 [1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2],
  certificateFrom 3459431 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3],
  certificateFrom 3459559 [1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2],
  certificateFrom 3461959 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6],
  certificateFrom 3464295 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2],
  certificateFrom 3470183 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2],
  certificateFrom 3471719 [1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3],
  certificateFrom 3478375 [1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2]]

private theorem checked26 : ∀ c ∈ cs26, Accepted c := by
  decide +kernel

private def cs27 : List Certificate :=
[  certificateFrom 3489895 [1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3],
  certificateFrom 3494567 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 1, 3],
  certificateFrom 3497127 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 3, 2],
  certificateFrom 3498727 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5],
  certificateFrom 3501223 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 3, 2],
  certificateFrom 3501799 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2],
  certificateFrom 3502759 [1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 3],
  certificateFrom 3502823 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5],
  certificateFrom 3506503 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2],
  certificateFrom 3506919 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3],
  certificateFrom 3509415 [1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 3, 2],
  certificateFrom 3509991 [1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2],
  certificateFrom 3510599 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2],
  certificateFrom 3514727 [1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4],
  certificateFrom 3518791 [1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2],
  certificateFrom 3522151 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3],
  certificateFrom 3526503 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6],
  certificateFrom 3528039 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3],
  certificateFrom 3530599 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4],
  certificateFrom 3532135 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3],
  certificateFrom 3532903 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2],
  certificateFrom 3533479 [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 1, 4],
  certificateFrom 3536807 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3],
  certificateFrom 3538023 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5],
  certificateFrom 3540327 [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3],
  certificateFrom 3540903 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3],
  certificateFrom 3544999 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3],
  certificateFrom 3556199 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3],
  certificateFrom 3556967 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4],
  certificateFrom 3558119 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2],
  certificateFrom 3559079 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 1, 5],
  certificateFrom 3560263 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3],
  certificateFrom 3560295 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3],
  certificateFrom 3564391 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3],
  certificateFrom 3565159 [1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4],
  certificateFrom 3568455 [1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3],
  certificateFrom 3573351 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2],
  certificateFrom 3575111 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4],
  certificateFrom 3575143 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2],
  certificateFrom 3577447 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2],
  certificateFrom 3579239 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2],
  certificateFrom 3585127 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6],
  certificateFrom 3585639 [1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2],
  certificateFrom 3603047 [1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3],
  certificateFrom 3607399 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4],
  certificateFrom 3613767 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 4, 2],
  certificateFrom 3614951 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2],
  certificateFrom 3615975 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5],
  certificateFrom 3618535 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4],
  certificateFrom 3620711 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5]]

private theorem checked27 : ∀ c ∈ cs27, Accepted c := by
  decide +kernel

private def cs28 : List Certificate :=
[  certificateFrom 3622375 [1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3],
  certificateFrom 3622631 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4],
  certificateFrom 3623015 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3],
  certificateFrom 3623143 [1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2],
  certificateFrom 3623751 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2],
  certificateFrom 3623783 [1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2],
  certificateFrom 3624807 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3],
  certificateFrom 3627111 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3],
  certificateFrom 3628903 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3],
  certificateFrom 3631175 [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3],
  certificateFrom 3631943 [1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2],
  certificateFrom 3635303 [1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3],
  certificateFrom 3635527 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4],
  certificateFrom 3642535 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 4, 2],
  certificateFrom 3647655 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 1, 5],
  certificateFrom 3648231 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3],
  certificateFrom 3659943 [1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 2, 3],
  certificateFrom 3666407 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5],
  certificateFrom 3667175 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2],
  certificateFrom 3670119 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4],
  certificateFrom 3671271 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2],
  certificateFrom 3673415 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3],
  certificateFrom 3674183 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 2],
  certificateFrom 3678311 [1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4],
  certificateFrom 3678695 [1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3],
  certificateFrom 3679463 [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2],
  certificateFrom 3681607 [1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3],
  certificateFrom 3683431 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3],
  certificateFrom 3684199 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2],
  certificateFrom 3686503 [1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2],
  certificateFrom 3688263 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4],
  certificateFrom 3691623 [1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3],
  certificateFrom 3695335 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2],
  certificateFrom 3699431 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2],
  certificateFrom 3702951 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 3, 2],
  certificateFrom 3703527 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2],
  certificateFrom 3708263 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4],
  certificateFrom 3716455 [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4],
  certificateFrom 3716839 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3],
  certificateFrom 3717031 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6],
  certificateFrom 3720935 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3],
  certificateFrom 3722343 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6],
  certificateFrom 3724647 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2],
  certificateFrom 3728743 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2],
  certificateFrom 3729127 [1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3],
  certificateFrom 3734631 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2],
  certificateFrom 3736935 [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2],
  certificateFrom 3742823 [1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2],
  certificateFrom 3748679 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4],
  certificateFrom 3755687 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 4, 2]]

private theorem checked28 : ∀ c ∈ cs28, Accepted c := by
  decide +kernel

private def cs29 : List Certificate :=
[  certificateFrom 3764295 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 1, 3],
  certificateFrom 3765063 [1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2],
  certificateFrom 3767463 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 4],
  certificateFrom 3768391 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 1, 3],
  certificateFrom 3773095 [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 3],
  certificateFrom 3774311 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3],
  certificateFrom 3776583 [1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 1, 3],
  certificateFrom 3776839 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4],
  certificateFrom 3777255 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5],
  certificateFrom 3780327 [1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2],
  certificateFrom 3783271 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4],
  certificateFrom 3786567 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3],
  certificateFrom 3788967 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3],
  certificateFrom 3791463 [1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4],
  certificateFrom 3794759 [1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3],
  certificateFrom 3797159 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 1, 3],
  certificateFrom 3799655 [1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2],
  certificateFrom 3809127 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4],
  certificateFrom 3811399 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 1, 4],
  certificateFrom 3812583 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2],
  certificateFrom 3814727 [1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3],
  certificateFrom 3815335 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3],
  certificateFrom 3816103 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 3, 2],
  certificateFrom 3817319 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2],
  certificateFrom 3819591 [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 1, 4],
  certificateFrom 3820647 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3],
  certificateFrom 3823527 [1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3],
  certificateFrom 3824359 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4],
  certificateFrom 3824743 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3],
  certificateFrom 3825511 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2],
  certificateFrom 3827783 [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2],
  certificateFrom 3828839 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3],
  certificateFrom 3836071 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 1, 4],
  certificateFrom 3840167 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 1, 4],
  certificateFrom 3844263 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 4, 2],
  certificateFrom 3845479 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4],
  certificateFrom 3848359 [1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 1, 4],
  certificateFrom 3849575 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4],
  certificateFrom 3854823 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4],
  certificateFrom 3855975 [1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2],
  certificateFrom 3856551 [1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2],
  certificateFrom 3857575 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 5],
  certificateFrom 3858919 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4],
  certificateFrom 3861671 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 1, 5],
  certificateFrom 3862247 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3],
  certificateFrom 3863015 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2],
  certificateFrom 3865767 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 2, 3],
  certificateFrom 3866951 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5],
  certificateFrom 3867111 [1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4],
  certificateFrom 3870023 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2]]

private theorem checked29 : ∀ c ∈ cs29, Accepted c := by
  decide +kernel

private def cs30 : List Certificate :=
[  certificateFrom 3871047 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5],
  certificateFrom 3871847 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4],
  certificateFrom 3875143 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3],
  certificateFrom 3875303 [1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2],
  certificateFrom 3878215 [1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2],
  certificateFrom 3878823 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2],
  certificateFrom 3887015 [1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 3, 2],
  certificateFrom 3888231 [1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2],
  certificateFrom 3891559 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3],
  certificateFrom 3893351 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5],
  certificateFrom 3893479 [1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2],
  certificateFrom 3894119 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2],
  certificateFrom 3897063 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4],
  certificateFrom 3898215 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2],
  certificateFrom 3899239 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7],
  certificateFrom 3899751 [1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3],
  certificateFrom 3905255 [1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4],
  certificateFrom 3905639 [1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3],
  certificateFrom 3906215 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 1, 3],
  certificateFrom 3906407 [1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2],
  certificateFrom 3910311 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3],
  certificateFrom 3913447 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2],
  certificateFrom 3914471 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5],
  certificateFrom 3917543 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2],
  certificateFrom 3918503 [1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3],
  certificateFrom 3918567 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5],
  certificateFrom 3922663 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3],
  certificateFrom 3925735 [1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2],
  certificateFrom 3926343 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2],
  certificateFrom 3930471 [1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4],
  certificateFrom 3933799 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3],
  certificateFrom 3937511 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4],
  certificateFrom 3937895 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3],
  certificateFrom 3939687 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5],
  certificateFrom 3941991 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3],
  certificateFrom 3943335 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 2, 4],
  certificateFrom 3947879 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3],
  certificateFrom 3950439 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4],
  certificateFrom 3953319 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 1, 4],
  certificateFrom 3961511 [1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 1, 4],
  certificateFrom 3969191 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 1, 6],
  certificateFrom 3969703 [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2],
  certificateFrom 3973863 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2],
  certificateFrom 3975399 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3],
  certificateFrom 3982055 [1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2],
  certificateFrom 3983175 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2],
  certificateFrom 3984199 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5],
  certificateFrom 3986759 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4],
  certificateFrom 3990599 [1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 1, 3],
  certificateFrom 3990855 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4]]

private theorem checked30 : ∀ c ∈ cs30, Accepted c := by
  decide +kernel

private def cs31 : List Certificate :=
[  certificateFrom 3991367 [1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2],
  certificateFrom 4000231 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4],
  certificateFrom 4003751 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4],
  certificateFrom 4007271 [1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2],
  certificateFrom 4016455 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3],
  certificateFrom 4019367 [1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 1, 3],
  certificateFrom 4020135 [1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2],
  certificateFrom 4023143 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4],
  certificateFrom 4027623 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5],
  certificateFrom 4031719 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5],
  certificateFrom 4034631 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 1, 5],
  certificateFrom 4035399 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2],
  certificateFrom 4035815 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3],
  certificateFrom 4039495 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2],
  certificateFrom 4040551 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5],
  certificateFrom 4041639 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 2, 3],
  certificateFrom 4044647 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5],
  certificateFrom 4046919 [1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 3],
  certificateFrom 4047687 [1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2],
  certificateFrom 4048743 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3],
  certificateFrom 4049831 [1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 2, 3],
  certificateFrom 4054183 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 2],
  certificateFrom 4058279 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 4, 2],
  certificateFrom 4062375 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2],
  certificateFrom 4063399 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 1, 5],
  certificateFrom 4063559 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2],
  certificateFrom 4063975 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3],
  certificateFrom 4067495 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 4, 3],
  certificateFrom 4067655 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2],
  certificateFrom 4071751 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2],
  certificateFrom 4075687 [1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 2, 3],
  certificateFrom 4076263 [1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3],
  certificateFrom 4081127 [1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4],
  certificateFrom 4081767 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4],
  certificateFrom 4085063 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3],
  certificateFrom 4085095 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3],
  certificateFrom 4085863 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4],
  certificateFrom 4089159 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3],
  certificateFrom 4089191 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3],
  certificateFrom 4089959 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2],
  certificateFrom 4093287 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3],
  certificateFrom 4094055 [1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4],
  certificateFrom 4097351 [1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3],
  certificateFrom 4098535 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3],
  certificateFrom 4102247 [1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2],
  certificateFrom 4102887 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4],
  certificateFrom 4106727 [1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3],
  certificateFrom 4106983 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4],
  certificateFrom 4111079 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2],
  certificateFrom 4114023 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6]]

private theorem checked31 : ∀ c ∈ cs31, Accepted c := by
  decide +kernel

private def cs32 : List Certificate :=
[  certificateFrom 4115175 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2],
  certificateFrom 4119271 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2],
  certificateFrom 4132519 [1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 1, 3],
  certificateFrom 4136103 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 5],
  certificateFrom 4136295 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2],
  certificateFrom 4144487 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2],
  certificateFrom 4145479 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5],
  certificateFrom 4148551 [1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2],
  certificateFrom 4158567 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2],
  certificateFrom 4162663 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2],
  certificateFrom 4164455 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4],
  certificateFrom 4170087 [1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3],
  certificateFrom 4170855 [1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2],
  certificateFrom 4176551 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 1, 5],
  certificateFrom 4180807 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2],
  certificateFrom 4185959 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3],
  certificateFrom 4188839 [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 3],
  certificateFrom 4189415 [1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3],
  certificateFrom 4192583 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4],
  certificateFrom 4192999 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7]]

private theorem checked32 : ∀ c ∈ cs32, Accepted c := by
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
  cs01 ++ (cs02 ++ (cs03 ++ (cs04 ++ (cs05 ++ (cs06 ++ (cs07 ++ (cs08 ++ (cs09 ++ (cs10 ++ (cs11 ++ (cs12 ++ (cs13 ++ (cs14 ++ (cs15 ++ (cs16 ++ (cs17 ++ (cs18 ++ (cs19 ++ (cs20 ++ (cs21 ++ (cs22 ++ (cs23 ++ (cs24 ++ (cs25 ++ (cs26 ++ (cs27 ++ (cs28 ++ (cs29 ++ (cs30 ++ (cs31 ++ (cs32)))))))))))))))))))))))))))))))

private theorem certificates_checked : ∀ c ∈ certificates, Accepted c := by
  exact append_checked checked01 (append_checked checked02 (append_checked checked03 (append_checked checked04 (append_checked checked05 (append_checked checked06 (append_checked checked07 (append_checked checked08 (append_checked checked09 (append_checked checked10 (append_checked checked11 (append_checked checked12 (append_checked checked13 (append_checked checked14 (append_checked checked15 (append_checked checked16 (append_checked checked17 (append_checked checked18 (append_checked checked19 (append_checked checked20 (append_checked checked21 (append_checked checked22 (append_checked checked23 (append_checked checked24 (append_checked checked25 (append_checked checked26 (append_checked checked27 (append_checked checked28 (append_checked checked29 (append_checked checked30 (append_checked checked31 (checked32)))))))))))))))))))))))))))))))

private def rawResidues : List ℕ :=
[  1767, 18023, 18791, 23911, 26215, 26791, 28743, 29927, 32839, 32871, 34023, 34663, 36167, 36935,
  38119, 38759, 41031, 42855, 43943, 44967, 45543, 46951, 49223, 51047, 52135, 60263, 61607, 64359,
  65703, 67399, 68455, 70983, 71015, 77991, 79175, 79591, 81511, 83687, 87367, 87783, 88391, 89703,
  91463, 92487, 93287, 96167, 96583, 99655, 100263, 100839, 108455, 108903, 109031, 111431, 111847, 112999,
  119655, 121191, 124775, 131175, 138407, 139367, 146023, 146599, 147623, 147783, 149319, 155975, 156007, 164199,
  169319, 170663, 171879, 172391, 174151, 174759, 177511, 178855, 182951, 191143, 198823, 201543, 202919, 205639,
  206439, 208231, 209735, 209767, 217575, 220519, 221671, 222823, 228519, 228711, 234599, 237895, 240807, 241575,
  244327, 250183, 252519, 255047, 256871, 259815, 260967, 263655, 265063, 270183, 271847, 272455, 272487, 276807,
  280647, 280903, 283815, 284999, 285415, 289095, 293191, 297127, 297703, 301223, 306535, 308455, 309415, 310631,
  314727, 315879, 316071, 316647, 319975, 322471, 324711, 327783, 328167, 328807, 332903, 335975, 338791, 340711,
  344231, 348327, 357735, 358119, 363335, 366311, 366503, 366919, 369991, 374119, 379239, 379367, 384103, 385895,
  391527, 396967, 398151, 398567, 402247, 404391, 406343, 410855, 411495, 413767, 414375, 421607, 422567, 423783,
  429799, 440935, 441959, 444519, 447815, 448615, 449127, 451911, 453863, 456007, 456615, 460711, 461287, 464807,
  465639, 469063, 469735, 474215, 476007, 477255, 477351, 480071, 480103, 484199, 485543, 493159, 493735, 496103,
  497255, 497831, 504295, 505447, 506023, 512487, 516583, 521319, 524775, 525415, 529511, 534759, 535399, 542183,
  542823, 542951, 543591, 544615, 546535, 546919, 555111, 555687, 562919, 563943, 567655, 568039, 571751, 575847,
  579943, 585799, 588135, 589895, 591719, 595815, 603239, 606311, 610983, 614567, 618407, 618663, 619175, 623335,
  625511, 628039, 631879, 637799, 638567, 640071, 644455, 648551, 650343, 653223, 653639, 656743, 657319, 660647,
  661415, 664423, 665927, 668519, 668839, 672615, 676679, 676711, 680807, 684103, 684871, 688199, 688231, 690023,
  694119, 696391, 699559, 708775, 708935, 713063, 713447, 716967, 717543, 719463, 722407, 723047, 725735, 726343,
  727719, 730599, 731239, 731815, 734535, 735143, 738791, 739431, 740455, 741223, 743527, 744551, 745319, 747591,
  748263, 748647, 751719, 754535, 756455, 763495, 764647, 766791, 773479, 773799, 776359, 779079, 781991, 782055,
  789831, 795111, 798023, 799847, 801383, 808039, 811367, 819559, 822087, 823143, 826023, 829511, 830119, 830695,
  833255, 833863, 837351, 837959, 838311, 838887, 845543, 853607, 854183, 857703, 858279, 861799, 862375, 864327,
  869607, 872519, 872935, 874343, 877031, 880711, 881127, 882535, 884807, 889511, 889959, 890727, 892999, 895207,
  902247, 902983, 905383, 910407, 911175, 913575, 914759, 914791, 928871, 931143, 931751, 932167, 932967, 936263,
  937063, 939175, 939943, 941159, 945255, 952679, 971431, 978663, 982183, 983783, 987303, 991559, 996071, 1004903,
  1006247, 1007975, 1008999, 1013095, 1014439, 1015399, 1016167, 1018983, 1021863, 1022055, 1022631, 1026727, 1034151, 1034407,
  1034919, 1039079, 1041255, 1050215, 1052327, 1053159, 1053543, 1054311, 1058407, 1064295, 1072295, 1076391, 1077159, 1081671,
  1084583, 1085767, 1090631, 1091815, 1093959, 1096551, 1098823, 1099879, 1103591, 1103975, 1105767, 1107015, 1108071, 1109223,
  1116487, 1119399, 1124679, 1124711, 1125095, 1127591, 1128807, 1132135, 1132711, 1132871, 1133287, 1135783, 1140903, 1150279,
  1151463, 1152231, 1154407, 1158055, 1159655, 1163335, 1165159, 1166247, 1171623, 1172199, 1176295, 1180391, 1183911, 1184487,
  1192103, 1192679, 1193703, 1197799, 1198919, 1201479, 1201511, 1201895, 1205575, 1205607, 1207111, 1209703, 1213767, 1214951,
  1221479, 1223015, 1223143, 1225575, 1227111, 1232551, 1235303, 1237831, 1240743, 1241159, 1242343, 1245255, 1246439, 1248935,
  1249351, 1251175, 1254631, 1259367, 1263431, 1269927, 1274023, 1278119, 1279463, 1280103, 1283431, 1286503, 1289447, 1297639,
  1302375, 1305255, 1305319, 1305703, 1305831, 1317991, 1319783, 1321127, 1323879, 1328743, 1330535, 1336935, 1337511, 1339879,
  1342631, 1346887, 1352007, 1354919, 1355495, 1356263, 1360999, 1364295, 1368423, 1377767, 1378407, 1379175, 1383079, 1384295,
  1385959, 1386599, 1387175, 1390311, 1391271, 1394407, 1398503, 1399527, 1403239, 1403623, 1407303, 1411431, 1411815, 1418855,
  1419623, 1420647, 1421383, 1423719, 1424743, 1428839, 1431143, 1431399, 1431911, 1441895, 1450087, 1453991, 1460039, 1462183,
  1468647, 1469287, 1471815, 1472231, 1473383, 1474151, 1477447, 1480039, 1481575, 1485927, 1488231, 1490023, 1492903, 1493319,
  1501511, 1504103, 1512295, 1512679, 1518503, 1519687, 1520455, 1520487, 1524967, 1525607, 1527879, 1529703, 1531047, 1535143,
  1537895, 1539239, 1540423, 1543335, 1544519, 1548615, 1551527, 1552711, 1555047, 1557223, 1560903, 1561927, 1563239, 1563303,
  1566023, 1566823, 1568615, 1570119, 1570151, 1574375, 1575399, 1580903, 1582439, 1582567, 1583175, 1583207, 1584231, 1588327,
  1591367, 1592039, 1596135, 1607847, 1608423, 1609063, 1610567, 1611943, 1613159, 1614663, 1617255, 1620135, 1621351, 1622855,
  1625447, 1626599, 1630695, 1638887, 1643623, 1647687, 1657671, 1661607, 1665863, 1668839, 1669799, 1673543, 1674055, 1676455,
  1677031, 1678055, 1699175, 1701095, 1702247, 1705191, 1708103, 1709287, 1713383, 1715111, 1718119, 1721575, 1722215, 1723719,
  1724487, 1725095, 1729255, 1732519, 1733287, 1733351, 1733735, 1734503, 1736871, 1737831, 1739623, 1745991, 1746023, 1751911,
  1754183, 1758535, 1758951, 1762631, 1766727, 1767751, 1768551, 1771239, 1771847, 1772007, 1774759, 1775527, 1776743, 1780039,
  1780071, 1782951, 1784167, 1784935, 1788263, 1789607, 1794919, 1802343, 1804135, 1814247, 1827559, 1831655, 1836871, 1839847,
  1840455, 1846503, 1850023, 1850983, 1851239, 1852903, 1853543, 1857639, 1859175, 1865639, 1865831, 1866407, 1869735, 1874663,
  1877927, 1878183, 1878759, 1880903, 1880935, 1887911, 1889127, 1889895, 1893191, 1896103, 1896935, 1912743, 1915495, 1916071,
  1920935, 1925447, 1927399, 1928039, 1929127, 1932135, 1934823, 1936231, 1940327, 1942599, 1943623, 1944807, 1948519, 1950791,
  1952999, 1960263, 1960295, 1964359, 1968295, 1971367, 1972391, 1976487, 1976647, 1979559, 1985895, 1987047, 1991143, 1994823,
  1995239, 1998183, 1998919, 1998951, 2000743, 2004071, 2004839, 2007111, 2007783, 2015975, 2016359, 2024167, 2027687, 2028263,
  2036455, 2037063, 2041191, 2045255, 2046279, 2058599, 2059367, 2061159, 2066791, 2069319, 2073415, 2077511, 2081607, 2084519,
  2085543, 2086119, 2088103, 2089799, 2091943, 2092199, 2092711, 2097479, 2101575, 2112103, 2117799, 2122087, 2123879, 2127175,
  2129511, 2130279, 2135975, 2136743, 2139463, 2140231, 2140839, 2141415, 2144999, 2145383, 2148263, 2148839, 2149031, 2149095,
  2149607, 2153575, 2155367, 2159463, 2164903, 2166119, 2167655, 2168999, 2170215, 2172519, 2173095, 2182471, 2183655, 2186407,
  2187751, 2190503, 2191079, 2191847, 2192487, 2195783, 2196583, 2198695, 2199271, 2199879, 2200679, 2204775, 2208071, 2212967,
  2213991, 2214727, 2218087, 2221127, 2222183, 2229991, 2239207, 2242887, 2246823, 2246983, 2247015, 2247399, 2249895, 2258151,
  2262247, 2262631, 2263399, 2264423, 2265159, 2265575, 2266727, 2268519, 2271079, 2274919, 2275175, 2282151, 2293927, 2295623,
  2303047, 2304231, 2306791, 2309735, 2312423, 2313031, 2313063, 2317927, 2321223, 2323815, 2324391, 2325607, 2326119, 2328487,
  2331815, 2332583, 2336679, 2344871, 2347879, 2351975, 2355271, 2356455, 2359367, 2360551, 2363047, 2363463, 2364263, 2365287,
  2366631, 2368743, 2373479, 2374823, 2375783, 2376007, 2383015, 2384039, 2384199, 2384615, 2387111, 2388135, 2388711, 2392231,
  2392391, 2392807, 2395303, 2396487, 2404679, 2407079, 2408295, 2410599, 2413927, 2414695, 2418023, 2418791, 2419815, 2419943,
  2423911, 2426215, 2432103, 2433895, 2435815, 2443431, 2444007, 2444967, 2448743, 2451623, 2454343, 2456935, 2462183, 2465127,
  2469607, 2469799, 2470375, 2482535, 2485095, 2488935, 2489191, 2492519, 2497191, 2501287, 2501863, 2505383, 2506599, 2509639,
  2512615, 2513223, 2514791, 2517063, 2517319, 2517735, 2517831, 2532967, 2533543, 2533735, 2536679, 2537831, 2544871, 2545255,
  2545831, 2546023, 2550695, 2551879, 2552295, 2553063, 2555975, 2557159, 2559303, 2560071, 2561895, 2564583, 2564839, 2565351,
  2567495, 2568103, 2570087, 2572455, 2576295, 2576551, 2577511, 2580647, 2582759, 2583399, 2584743, 2587495, 2588839, 2595687,
  2598215, 2602727, 2606823, 2607431, 2607591, 2612327, 2615015, 2615623, 2616423, 2626375, 2628711, 2630471, 2630503, 2633799,
  2634599, 2643815, 2649831, 2658023, 2658983, 2662567, 2663143, 2665639, 2666215, 2671335, 2672455, 2675015, 2679143, 2680647,
  2684263, 2688487, 2689127, 2693799, 2696551, 2696679, 2697319, 2697895, 2698343, 2701991, 2702055, 2709415, 2714343, 2721383,
  2722535, 2724679, 2725479, 2728775, 2729575, 2733671, 2736967, 2739559, 2741863, 2743463, 2747559, 2749543, 2751655, 2752839,
  2753639, 2756935, 2761031, 2762983, 2763623, 2764711, 2771175, 2771815, 2772903, 2775719, 2779239, 2779367, 2780007, 2784103,
  2788167, 2791527, 2792295, 2800359, 2804039, 2804071, 2804455, 2808551, 2812231, 2825575, 2828135, 2830407, 2833767, 2834535,
  2835687, 2837831, 2838599, 2840423, 2847847, 2848615, 2851559, 2851943, 2860135, 2866791, 2867943, 2870087, 2872679, 2873063,
  2876775, 2880839, 2880871, 2881447, 2884967, 2885351, 2885543, 2885959, 2893159, 2894183, 2894951, 2898279, 2899047, 2900839,
  2902375, 2904903, 2904935, 2913095, 2913511, 2917607, 2920519, 2921287, 2921703, 2923687, 2925383, 2926439, 2927527, 2930535,
  2932807, 2933063, 2933575, 2934631, 2935719, 2947687, 2949287, 2950983, 2961575, 2965095, 2969447, 2970951, 2972327, 2973287,
  2973543, 2975047, 2975815, 2979751, 2980519, 2983239, 2983847, 2984423, 2992039, 2992615, 2995047, 3003239, 3004583, 3005799,
  3018055, 3021991, 3023335, 3026247, 3028071, 3030183, 3031367, 3034439, 3036263, 3039559, 3043239, 3044455, 3048551, 3048935,
  3055975, 3056711, 3056743, 3061479, 3062439, 3062631, 3064903, 3065575, 3069671, 3070279, 3073767, 3074727, 3081959, 3082567,
  3085479, 3090759, 3090791, 3093671, 3093735, 3094887, 3098983, 3100007, 3104103, 3106407, 3112295, 3117735, 3125159, 3129511,
  3131207, 3133607, 3138279, 3139399, 3140455, 3142375, 3144551, 3147591, 3148647, 3150567, 3159975, 3161703, 3165287, 3168167,
  3168583, 3169383, 3169895, 3172679, 3172711, 3176359, 3176775, 3180455, 3188647, 3191655, 3192039, 3198631, 3199847, 3200231,
  3203911, 3206055, 3206823, 3206887, 3210407, 3211367, 3219559, 3219783, 3226791, 3227815, 3231911, 3236167, 3241287, 3245543,
  3250279, 3253575, 3255527, 3257703, 3259495, 3262951, 3263719, 3267303, 3267687, 3273575, 3278439, 3281735, 3282535, 3285831,
  3287207, 3289927, 3292519, 3296615, 3305191, 3305959, 3308903, 3313383, 3320039, 3320679, 3324519, 3327079, 3332711, 3352647,
  3360839, 3369319, 3376743, 3377319, 3377511, 3378535, 3380455, 3380839, 3381415, 3386279, 3389031, 3389607, 3391559, 3393383,
  3394471, 3396071, 3396839, 3400167, 3402663, 3404903, 3408359, 3408615, 3408999, 3412135, 3413095, 3417159, 3418343, 3418983,
  3420327, 3426535, 3427175, 3428519, 3429703, 3429735, 3433799, 3433831, 3437895, 3440231, 3441991, 3443175, 3445927, 3446503,
  3450183, 3451367, 3456103, 3457895, 3458983, 3459431, 3459559, 3461959, 3464295, 3470183, 3471719, 3478375, 3489895, 3494567,
  3497127, 3498727, 3501223, 3501799, 3502759, 3502823, 3506503, 3506919, 3509415, 3509991, 3510599, 3514727, 3518791, 3522151,
  3526503, 3528039, 3530599, 3532135, 3532903, 3533479, 3536807, 3538023, 3540327, 3540903, 3544999, 3556199, 3556967, 3558119,
  3559079, 3560263, 3560295, 3564391, 3565159, 3568455, 3573351, 3575111, 3575143, 3577447, 3579239, 3585127, 3585639, 3603047,
  3607399, 3613767, 3614951, 3615975, 3618535, 3620711, 3622375, 3622631, 3623015, 3623143, 3623751, 3623783, 3624807, 3627111,
  3628903, 3631175, 3631943, 3635303, 3635527, 3642535, 3647655, 3648231, 3659943, 3666407, 3667175, 3670119, 3671271, 3673415,
  3674183, 3678311, 3678695, 3679463, 3681607, 3683431, 3684199, 3686503, 3688263, 3691623, 3695335, 3699431, 3702951, 3703527,
  3708263, 3716455, 3716839, 3717031, 3720935, 3722343, 3724647, 3728743, 3729127, 3734631, 3736935, 3742823, 3748679, 3755687,
  3764295, 3765063, 3767463, 3768391, 3773095, 3774311, 3776583, 3776839, 3777255, 3780327, 3783271, 3786567, 3788967, 3791463,
  3794759, 3797159, 3799655, 3809127, 3811399, 3812583, 3814727, 3815335, 3816103, 3817319, 3819591, 3820647, 3823527, 3824359,
  3824743, 3825511, 3827783, 3828839, 3836071, 3840167, 3844263, 3845479, 3848359, 3849575, 3854823, 3855975, 3856551, 3857575,
  3858919, 3861671, 3862247, 3863015, 3865767, 3866951, 3867111, 3870023, 3871047, 3871847, 3875143, 3875303, 3878215, 3878823,
  3887015, 3888231, 3891559, 3893351, 3893479, 3894119, 3897063, 3898215, 3899239, 3899751, 3905255, 3905639, 3906215, 3906407,
  3910311, 3913447, 3914471, 3917543, 3918503, 3918567, 3922663, 3925735, 3926343, 3930471, 3933799, 3937511, 3937895, 3939687,
  3941991, 3943335, 3947879, 3950439, 3953319, 3961511, 3969191, 3969703, 3973863, 3975399, 3982055, 3983175, 3984199, 3986759,
  3990599, 3990855, 3991367, 4000231, 4003751, 4007271, 4016455, 4019367, 4020135, 4023143, 4027623, 4031719, 4034631, 4035399,
  4035815, 4039495, 4040551, 4041639, 4044647, 4046919, 4047687, 4048743, 4049831, 4054183, 4058279, 4062375, 4063399, 4063559,
  4063975, 4067495, 4067655, 4071751, 4075687, 4076263, 4081127, 4081767, 4085063, 4085095, 4085863, 4089159, 4089191, 4089959,
  4093287, 4094055, 4097351, 4098535, 4102247, 4102887, 4106727, 4106983, 4111079, 4114023, 4115175, 4119271, 4132519, 4136103,
  4136295, 4144487, 4145479, 4148551, 4158567, 4162663, 4164455, 4170087, 4170855, 4176551, 4180807, 4185959, 4188839, 4189415,
  4192583, 4192999]

private theorem certificateFrom_residue (r : ℕ) (es : List ℕ) :
    (certificateFrom r es).residue = r := by
  rfl

private theorem residue_map :
    certificates.map Certificate.residue = rawResidues := by
  simp only [certificates, cs01, cs02, cs03, cs04, cs05, cs06, cs07, cs08, cs09, cs10, cs11, cs12, cs13, cs14, cs15, cs16, cs17, cs18, cs19, cs20, cs21, cs22, cs23, cs24, cs25, cs26, cs27, cs28, cs29, cs30, cs31, cs32, rawResidues,
    List.map_append, List.map_cons, List.map_nil, certificateFrom_residue,
    List.cons_append, List.nil_append]

private theorem target_mem_iff (r : ℕ) :
    r ∈ syracuseSevenMod32New22Step13Classes ↔ r ∈ rawResidues := by
  simp only [syracuseSevenMod32New22Step13Classes, rawResidues,
    Finset.mem_insert, Finset.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]

end Session67Parents

theorem solution (n : ℕ)
    (h : n % 4194304 ∈ syracuseSevenMod32New22Step13Classes) :
    syracuseStep^[13] n < n := by
  have hr : n % 4194304 ∈ Session67Parents.rawResidues :=
    (Session67Parents.target_mem_iff _).mp h
  have hc : n % 4194304 ∈
      Session67Parents.Batch.residues Session67Parents.certificates := by
    simpa only [Session67Parents.Batch.residues, Session67Parents.residue_map] using hr
  exact Session67Parents.Batch.descent_of_mem Session67Parents.certificates
    Session67Parents.certificates_checked n hc

#print axioms Session67Parents.certificates_checked
#print axioms solution
