-- Prove2me | solution 1 for syracuse_descent_new21_step12_seven_mod32
-- status  : ACCEPTED   (prove)
-- author  : @FakeMink
-- created : 2026-10-01T16:06:27.873628+00:00
-- url     : https://prove2.me/submissions/a541b357-5308-4adb-8615-c3870496642c

import Definitions.Def_syracuseSevenMod32New21Step12Classes
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
  Valid 2097152 c.residue c.endA c.endB c.trace ∧
  c.trace.length = 12 ∧ c.endA ≤ 2097152 ∧ c.endB < c.residue

instance (c : Certificate) : Decidable (Accepted c) := by
  unfold Accepted
  infer_instance

def residues (cs : List Certificate) : List ℕ := cs.map Certificate.residue

theorem descent_of_accepted {c : Certificate} (h : Accepted c) (k : ℕ) :
    syracuseStep^[12] (2097152 * k + c.residue) < 2097152 * k + c.residue := by
  rcases h with ⟨hvalid, hlength, ha, hb⟩
  simpa only [hlength] using AffineTrace.strict_descent hvalid ha hb k

theorem descent_of_residue {c : Certificate} (h : Accepted c)
    (n : ℕ) (hn : n % 2097152 = c.residue) : syracuseStep^[12] n < n := by
  have hform : n = 2097152 * (n / 2097152) + c.residue := by omega
  rw [hform]
  exact descent_of_accepted h (n / 2097152)

/-- The proof consumes finite, kernel-checked certificate acceptance, not search output. -/
theorem descent_of_mem (cs : List Certificate) (hchecked : ∀ c ∈ cs, Accepted c)
    (n : ℕ) (h : n % 2097152 ∈ residues cs) : syracuseStep^[12] n < n := by
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
  let result := traceFrom 2097152 r es
  ⟨r, result.1, result.2.1, result.2.2⟩

def certificates : List Certificate :=
[  certificateFrom 1255 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4],
  certificateFrom 1511 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3],
  certificateFrom 4167 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 4],
  certificateFrom 8039 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6],
  certificateFrom 9447 [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4],
  certificateFrom 9703 [1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3],
  certificateFrom 10311 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 4],
  certificateFrom 10343 [1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3],
  certificateFrom 14183 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4],
  certificateFrom 16487 [1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3],
  certificateFrom 18503 [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 4],
  certificateFrom 23271 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5],
  certificateFrom 25319 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5],
  certificateFrom 29415 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5],
  certificateFrom 32935 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 4],
  certificateFrom 33511 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3],
  certificateFrom 34983 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 4],
  certificateFrom 35559 [1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3],
  certificateFrom 39079 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 4],
  certificateFrom 44391 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7],
  certificateFrom 47271 [1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 4],
  certificateFrom 48487 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5],
  certificateFrom 52583 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3],
  certificateFrom 53735 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4],
  certificateFrom 54631 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3],
  certificateFrom 57831 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4],
  certificateFrom 58727 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3],
  certificateFrom 64615 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6],
  certificateFrom 66023 [1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4],
  certificateFrom 66919 [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3],
  certificateFrom 70759 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4],
  certificateFrom 72807 [1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4],
  certificateFrom 85671 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 5],
  certificateFrom 95047 [1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3],
  certificateFrom 95975 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6],
  certificateFrom 101191 [1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3],
  certificateFrom 104167 [1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4],
  certificateFrom 110311 [1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4],
  certificateFrom 129383 [1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4],
  certificateFrom 129639 [1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3],
  certificateFrom 136423 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5],
  certificateFrom 142247 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 5],
  certificateFrom 142567 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5],
  certificateFrom 146087 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 4],
  certificateFrom 147303 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7],
  certificateFrom 148711 [1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3],
  certificateFrom 149351 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5],
  certificateFrom 151623 [1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 3],
  certificateFrom 152231 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 4],
  certificateFrom 155495 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3],
  certificateFrom 157767 [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 3],
  certificateFrom 160423 [1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 4],
  certificateFrom 161639 [1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3],
  certificateFrom 174247 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 5],
  certificateFrom 185671 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5],
  certificateFrom 185959 [1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4],
  certificateFrom 186535 [1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 3],
  certificateFrom 189767 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5],
  certificateFrom 192999 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5],
  certificateFrom 193863 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3],
  certificateFrom 199143 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5],
  certificateFrom 200007 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3],
  certificateFrom 202663 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 4],
  certificateFrom 205287 [1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3],
  certificateFrom 208199 [1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3],
  certificateFrom 208807 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 4],
  certificateFrom 212071 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3],
  certificateFrom 216999 [1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 4],
  certificateFrom 218215 [1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3],
  certificateFrom 222055 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4],
  certificateFrom 223463 [1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4],
  certificateFrom 224103 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4],
  certificateFrom 228199 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4],
  certificateFrom 236391 [1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4],
  certificateFrom 243431 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3],
  certificateFrom 247527 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3],
  certificateFrom 255719 [1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3],
  certificateFrom 256327 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4],
  certificateFrom 280039 [1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4],
  certificateFrom 280679 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4],
  certificateFrom 284775 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4],
  certificateFrom 292967 [1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4],
  certificateFrom 293543 [1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 3],
  certificateFrom 299687 [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 3],
  certificateFrom 301799 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6],
  certificateFrom 303847 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6],
  certificateFrom 305895 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4],
  certificateFrom 312039 [1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4],
  certificateFrom 313159 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3],
  certificateFrom 321351 [1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3],
  certificateFrom 337255 [1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4],
  certificateFrom 350119 [1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 3],
  certificateFrom 356263 [1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 3],
  certificateFrom 363367 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5],
  certificateFrom 365383 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4],
  certificateFrom 369479 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4],
  certificateFrom 369735 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 3],
  certificateFrom 375655 [1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3],
  certificateFrom 377671 [1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4],
  certificateFrom 377927 [1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 3],
  certificateFrom 384167 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 5],
  certificateFrom 388263 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 5],
  certificateFrom 391495 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5],
  certificateFrom 392359 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 3],
  certificateFrom 393543 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5],
  certificateFrom 397639 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5],
  certificateFrom 398503 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 3],
  certificateFrom 401735 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3],
  certificateFrom 403783 [1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3],
  certificateFrom 406695 [1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 3],
  certificateFrom 419943 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5],
  certificateFrom 421959 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 4],
  certificateFrom 426055 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 4],
  certificateFrom 426087 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5],
  certificateFrom 427879 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6],
  certificateFrom 431975 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4],
  certificateFrom 432231 [1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3],
  certificateFrom 434247 [1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 4],
  certificateFrom 441063 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7],
  certificateFrom 445159 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5],
  certificateFrom 449255 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3],
  certificateFrom 451303 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3],
  certificateFrom 454823 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 4],
  certificateFrom 455399 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3],
  certificateFrom 463591 [1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3],
  certificateFrom 464199 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6],
  certificateFrom 466279 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5],
  certificateFrom 472391 [1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4],
  certificateFrom 474471 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3],
  certificateFrom 478535 [1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4],
  certificateFrom 486503 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4],
  certificateFrom 488551 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4],
  certificateFrom 492647 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4],
  certificateFrom 500839 [1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4],
  certificateFrom 504647 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5],
  certificateFrom 510791 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5],
  certificateFrom 511655 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 3],
  certificateFrom 516935 [1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3],
  certificateFrom 519847 [1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 3],
  certificateFrom 526055 [1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4],
  certificateFrom 539239 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5],
  certificateFrom 543079 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4],
  certificateFrom 549223 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4],
  certificateFrom 554215 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5],
  certificateFrom 557415 [1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4],
  certificateFrom 558311 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5],
  certificateFrom 561223 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 5],
  certificateFrom 562407 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3],
  certificateFrom 563879 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 4],
  certificateFrom 567143 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7],
  certificateFrom 567367 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 5],
  certificateFrom 567975 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 4],
  certificateFrom 568231 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 3],
  certificateFrom 568551 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3],
  certificateFrom 571239 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5],
  certificateFrom 573511 [1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 3],
  certificateFrom 575335 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3],
  certificateFrom 576167 [1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 4],
  certificateFrom 576423 [1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 3],
  certificateFrom 576743 [1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3],
  certificateFrom 589991 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 5],
  certificateFrom 591687 [1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4],
  certificateFrom 592039 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 5],
  certificateFrom 596135 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 5],
  certificateFrom 599655 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4],
  certificateFrom 600231 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 3],
  certificateFrom 602279 [1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 3],
  certificateFrom 605799 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4],
  certificateFrom 610791 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5],
  certificateFrom 611655 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3],
  certificateFrom 613991 [1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4],
  certificateFrom 614887 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5],
  certificateFrom 615751 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3],
  certificateFrom 618983 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3],
  certificateFrom 620455 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 4],
  certificateFrom 623943 [1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3],
  certificateFrom 624551 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 4],
  certificateFrom 625127 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3],
  certificateFrom 627815 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5],
  certificateFrom 632743 [1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 4],
  certificateFrom 633319 [1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3],
  certificateFrom 640103 [1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3],
  certificateFrom 643943 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4],
  certificateFrom 648263 [1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 4],
  certificateFrom 662695 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 6],
  certificateFrom 670023 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6],
  certificateFrom 670887 [1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 4],
  certificateFrom 672071 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6],
  certificateFrom 674119 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4],
  certificateFrom 677031 [1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 4],
  certificateFrom 680263 [1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4],
  certificateFrom 690535 [1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3],
  certificateFrom 696679 [1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3],
  certificateFrom 703143 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 5],
  certificateFrom 709287 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 5],
  certificateFrom 715431 [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 3],
  certificateFrom 733927 [1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4],
  certificateFrom 744807 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6],
  certificateFrom 747111 [1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3],
  certificateFrom 750951 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4],
  certificateFrom 752999 [1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4],
  certificateFrom 753255 [1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3],
  certificateFrom 759719 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 5],
  certificateFrom 765863 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 5],
  certificateFrom 772007 [1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 3],
  certificateFrom 779111 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5],
  certificateFrom 781159 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5],
  certificateFrom 785255 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5],
  certificateFrom 789351 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3],
  certificateFrom 790183 [1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 4],
  certificateFrom 791399 [1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3],
  certificateFrom 809287 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7],
  certificateFrom 810151 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 3],
  certificateFrom 813383 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5],
  certificateFrom 814247 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 3],
  certificateFrom 817479 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3],
  certificateFrom 819527 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3],
  certificateFrom 822439 [1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 3],
  certificateFrom 823623 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3],
  certificateFrom 831815 [1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3],
  certificateFrom 832743 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6],
  certificateFrom 837735 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5],
  certificateFrom 840935 [1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4],
  certificateFrom 841831 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5],
  certificateFrom 845927 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3],
  certificateFrom 846759 [1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 4],
  certificateFrom 847079 [1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4],
  certificateFrom 852071 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3],
  certificateFrom 860263 [1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3],
  certificateFrom 862951 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5],
  certificateFrom 868519 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 6],
  certificateFrom 870567 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 6],
  certificateFrom 871143 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3],
  certificateFrom 872615 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 4],
  certificateFrom 878759 [1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 4],
  certificateFrom 889319 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6],
  certificateFrom 892263 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3],
  certificateFrom 894279 [1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4],
  certificateFrom 897511 [1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4],
  certificateFrom 898407 [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3],
  certificateFrom 903655 [1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4],
  certificateFrom 908391 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4],
  certificateFrom 922439 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5],
  certificateFrom 926535 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5],
  certificateFrom 930631 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3],
  certificateFrom 936775 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3],
  certificateFrom 939751 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4],
  certificateFrom 944967 [1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3],
  certificateFrom 945895 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4],
  certificateFrom 954087 [1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4],
  certificateFrom 960871 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4],
  certificateFrom 964967 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4],
  certificateFrom 965223 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3],
  certificateFrom 973159 [1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4],
  certificateFrom 973415 [1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3],
  certificateFrom 979015 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 5],
  certificateFrom 980199 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3],
  certificateFrom 983111 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 5],
  certificateFrom 984295 [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3],
  certificateFrom 987207 [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 3],
  certificateFrom 989031 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5],
  certificateFrom 992487 [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3],
  certificateFrom 993351 [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 3],
  certificateFrom 997223 [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3],
  certificateFrom 1001543 [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 3],
  certificateFrom 1007783 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 7],
  certificateFrom 1011879 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 5],
  certificateFrom 1015975 [1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 3],
  certificateFrom 1017447 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4],
  certificateFrom 1018023 [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 3],
  certificateFrom 1021543 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4],
  certificateFrom 1022119 [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 3],
  certificateFrom 1029735 [1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4],
  certificateFrom 1030311 [1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 3],
  certificateFrom 1036775 [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3],
  certificateFrom 1040871 [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3],
  certificateFrom 1043559 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5],
  certificateFrom 1045607 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5],
  certificateFrom 1049063 [1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3],
  certificateFrom 1049703 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5],
  certificateFrom 1053799 [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3],
  certificateFrom 1055847 [1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3],
  certificateFrom 1057639 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6],
  certificateFrom 1059047 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4],
  certificateFrom 1059687 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6],
  certificateFrom 1061735 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4],
  certificateFrom 1067239 [1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4],
  certificateFrom 1067879 [1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4],
  certificateFrom 1087207 [1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3],
  certificateFrom 1092775 [1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 4],
  certificateFrom 1093351 [1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3],
  certificateFrom 1100135 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5],
  certificateFrom 1102151 [1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4],
  certificateFrom 1106279 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5],
  certificateFrom 1112423 [1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3],
  certificateFrom 1115623 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4],
  certificateFrom 1116263 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6],
  certificateFrom 1120935 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 5],
  certificateFrom 1123815 [1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4],
  certificateFrom 1124455 [1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4],
  certificateFrom 1125031 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 5],
  certificateFrom 1129127 [1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 3],
  certificateFrom 1130599 [1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4],
  certificateFrom 1135271 [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 3],
  certificateFrom 1141479 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6],
  certificateFrom 1143463 [1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 3],
  certificateFrom 1147623 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4],
  certificateFrom 1149671 [1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4],
  certificateFrom 1156711 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5],
  certificateFrom 1162855 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5],
  certificateFrom 1166695 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4],
  certificateFrom 1168743 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4],
  certificateFrom 1168999 [1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3],
  certificateFrom 1172839 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4],
  certificateFrom 1177511 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 5],
  certificateFrom 1181031 [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4],
  certificateFrom 1181607 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 5],
  certificateFrom 1185703 [1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 3],
  certificateFrom 1191847 [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 3],
  certificateFrom 1196903 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7],
  certificateFrom 1200039 [1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 3],
  certificateFrom 1200967 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6],
  certificateFrom 1200999 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5],
  certificateFrom 1205095 [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3],
  certificateFrom 1206503 [1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3],
  certificateFrom 1207143 [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3],
  certificateFrom 1209159 [1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4],
  certificateFrom 1211239 [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3],
  certificateFrom 1215303 [1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4],
  certificateFrom 1219431 [1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3],
  certificateFrom 1231175 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5],
  certificateFrom 1239367 [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3],
  certificateFrom 1243751 [1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4],
  certificateFrom 1257543 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 6],
  certificateFrom 1262823 [1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4],
  certificateFrom 1263079 [1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3],
  certificateFrom 1263719 [1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3],
  certificateFrom 1265511 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8],
  certificateFrom 1265735 [1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 4],
  certificateFrom 1267559 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6],
  certificateFrom 1267815 [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3],
  certificateFrom 1269607 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4],
  certificateFrom 1271879 [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 4],
  certificateFrom 1275751 [1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4],
  certificateFrom 1276007 [1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3],
  certificateFrom 1288935 [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3],
  certificateFrom 1295079 [1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3],
  certificateFrom 1300647 [1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 4],
  certificateFrom 1307975 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4],
  certificateFrom 1308007 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5],
  certificateFrom 1314119 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4],
  certificateFrom 1319399 [1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4],
  certificateFrom 1320295 [1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3],
  certificateFrom 1322087 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6],
  certificateFrom 1322311 [1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4],
  certificateFrom 1324135 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6],
  certificateFrom 1326183 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4],
  certificateFrom 1332327 [1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4],
  certificateFrom 1348423 [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3],
  certificateFrom 1352519 [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3],
  certificateFrom 1357543 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4],
  certificateFrom 1360711 [1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3],
  certificateFrom 1361639 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4],
  certificateFrom 1369831 [1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4],
  certificateFrom 1399463 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 6],
  certificateFrom 1404999 [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 3],
  certificateFrom 1407655 [1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 4],
  certificateFrom 1409095 [1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 3],
  certificateFrom 1413799 [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 4],
  certificateFrom 1415015 [1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3],
  certificateFrom 1417287 [1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 3],
  certificateFrom 1427271 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4],
  certificateFrom 1429671 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 5],
  certificateFrom 1435463 [1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4],
  certificateFrom 1437863 [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 3],
  certificateFrom 1455431 [1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3],
  certificateFrom 1456039 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 6],
  certificateFrom 1461351 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7],
  certificateFrom 1461575 [1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3],
  certificateFrom 1464231 [1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 4],
  certificateFrom 1465447 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5],
  certificateFrom 1469543 [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3],
  certificateFrom 1470375 [1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 4],
  certificateFrom 1471591 [1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3],
  certificateFrom 1475687 [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3],
  certificateFrom 1483847 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 4],
  certificateFrom 1483879 [1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3],
  certificateFrom 1489767 [1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4],
  certificateFrom 1492039 [1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 4],
  certificateFrom 1496807 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5],
  certificateFrom 1502951 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5],
  certificateFrom 1506471 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 4],
  certificateFrom 1509095 [1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3],
  certificateFrom 1509703 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6],
  certificateFrom 1512615 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 4],
  certificateFrom 1515847 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4],
  certificateFrom 1517895 [1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4],
  certificateFrom 1517927 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5],
  certificateFrom 1520807 [1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 4],
  certificateFrom 1522023 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5],
  certificateFrom 1526119 [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3],
  certificateFrom 1532263 [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3],
  certificateFrom 1540455 [1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3],
  certificateFrom 1546343 [1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4],
  certificateFrom 1546919 [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 3],
  certificateFrom 1551015 [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 3],
  certificateFrom 1559207 [1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 3],
  certificateFrom 1563367 [1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4],
  certificateFrom 1565415 [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4],
  certificateFrom 1569511 [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4],
  certificateFrom 1574503 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5],
  certificateFrom 1574727 [1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3],
  certificateFrom 1577703 [1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4],
  certificateFrom 1578599 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5],
  certificateFrom 1582695 [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3],
  certificateFrom 1588583 [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4],
  certificateFrom 1588839 [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3],
  certificateFrom 1597031 [1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3],
  certificateFrom 1603495 [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 3],
  certificateFrom 1607591 [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 3],
  certificateFrom 1615783 [1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 3],
  certificateFrom 1616103 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5],
  certificateFrom 1618791 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5],
  certificateFrom 1625767 [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 4],
  certificateFrom 1626983 [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3],
  certificateFrom 1631047 [1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4],
  certificateFrom 1631303 [1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 3],
  certificateFrom 1633959 [1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 4],
  certificateFrom 1653927 [1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 3],
  certificateFrom 1657159 [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3],
  certificateFrom 1660071 [1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 3],
  certificateFrom 1663303 [1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3],
  certificateFrom 1672679 [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5],
  certificateFrom 1676519 [1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4],
  certificateFrom 1682343 [1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 4],
  certificateFrom 1682663 [1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4],
  certificateFrom 1687623 [1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 4],
  certificateFrom 1689447 [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4],
  certificateFrom 1690535 [1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 4],
  certificateFrom 1690855 [1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4],
  certificateFrom 1704679 [1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5],
  certificateFrom 1708199 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 6],
  certificateFrom 1714343 [1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 4],
  certificateFrom 1716391 [1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 4],
  certificateFrom 1716967 [1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3],
  certificateFrom 1723751 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5],
  certificateFrom 1725767 [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4],
  certificateFrom 1725799 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5],
  certificateFrom 1729863 [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4],
  certificateFrom 1729895 [1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5],
  certificateFrom 1733095 [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4],
  certificateFrom 1733991 [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3],
  certificateFrom 1736039 [1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3],
  certificateFrom 1738055 [1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4],
  certificateFrom 1739239 [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4],
  certificateFrom 1747431 [1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4],
  certificateFrom 1754215 [1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4],
  certificateFrom 1773223 [1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 3],
  certificateFrom 1796455 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6],
  certificateFrom 1804647 [1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4],
  certificateFrom 1810791 [1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4],
  certificateFrom 1823975 [1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3],
  certificateFrom 1826663 [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5],
  certificateFrom 1829543 [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 4],
  certificateFrom 1829799 [1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 3],
  certificateFrom 1830119 [1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3],
  certificateFrom 1853031 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6],
  certificateFrom 1855655 [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 3],
  certificateFrom 1861223 [1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4],
  certificateFrom 1861799 [1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 3],
  certificateFrom 1865031 [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5],
  certificateFrom 1867367 [1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4],
  certificateFrom 1871175 [1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5],
  certificateFrom 1877319 [1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3],
  certificateFrom 1880551 [1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3],
  certificateFrom 1883239 [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5],
  certificateFrom 1886119 [1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 4],
  certificateFrom 1886695 [1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3],
  certificateFrom 1891431 [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3],
  certificateFrom 1897319 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6],
  certificateFrom 1903463 [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4],
  certificateFrom 1905511 [1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4],
  certificateFrom 1914599 [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5],
  certificateFrom 1918695 [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5],
  certificateFrom 1922791 [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3],
  certificateFrom 1924263 [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 4],
  certificateFrom 1928359 [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 4],
  certificateFrom 1928935 [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3],
  certificateFrom 1931591 [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4],
  certificateFrom 1933639 [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4],
  certificateFrom 1936551 [1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 4],
  certificateFrom 1937127 [1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3],
  certificateFrom 1937735 [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4],
  certificateFrom 1943911 [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3],
  certificateFrom 1945927 [1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4],
  certificateFrom 1948007 [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3],
  certificateFrom 1956199 [1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3],
  certificateFrom 1960039 [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4],
  certificateFrom 1966183 [1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4],
  certificateFrom 1974375 [1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4],
  certificateFrom 1984327 [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5],
  certificateFrom 1985255 [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4],
  certificateFrom 2000487 [1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3],
  certificateFrom 2002279 [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6],
  certificateFrom 2004327 [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6],
  certificateFrom 2004583 [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3],
  certificateFrom 2006375 [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4],
  certificateFrom 2012519 [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4],
  certificateFrom 2012775 [1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3],
  certificateFrom 2040903 [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 5],
  certificateFrom 2042087 [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3],
  certificateFrom 2044743 [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4],
  certificateFrom 2044775 [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3],
  certificateFrom 2050279 [1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3],
  certificateFrom 2050887 [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4],
  certificateFrom 2050919 [1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3],
  certificateFrom 2059079 [1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4],
  certificateFrom 2063527 [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 5],
  certificateFrom 2069671 [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 5],
  certificateFrom 2072903 [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5],
  certificateFrom 2075815 [1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 3],
  certificateFrom 2079335 [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4],
  certificateFrom 2085191 [1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3],
  certificateFrom 2087527 [1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4],
  certificateFrom 2094311 [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4]]

theorem certificates_checked : ∀ c ∈ certificates, Accepted c := by
  decide +kernel

theorem coverage : (certificates.map Certificate.residue).toFinset =
    syracuseSevenMod32New21Step12Classes := by
  decide +kernel

end Session67Parents

theorem solution (n : ℕ)
    (h : n % 2097152 ∈ syracuseSevenMod32New21Step12Classes) :
    syracuseStep^[12] n < n := by
  rw [← Session67Parents.coverage] at h
  exact Session67Parents.Batch.descent_of_mem Session67Parents.certificates
    Session67Parents.certificates_checked n (List.mem_toFinset.mp h)

#print axioms Session67Parents.certificates_checked
#print axioms solution
