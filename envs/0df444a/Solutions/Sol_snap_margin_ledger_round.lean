-- Prove2me | solution 1 for snap_margin_ledger_round
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:13:17.75311+00:00
-- url     : https://prove2.me/submissions/e14d2b80-4267-4598-9db6-8a18ae6c0dc2

import Mathlib

/-!
# Snap displacement versus the recorded margin (the margin–ledger joint)

An ellipsoid/separation loop records, per round, a cut normal `c`, a margin `del`, and a centre.
The separation oracle is evaluated at a **snapped** centre `a` (the rational grid point), while the
engine's recorded centre `a'` is the exact iterate. This file proves the exact accounting:

* a cut separating a set `S` around `a` with margin `m` separates it around `a'` with margin
  `m + C·ε`, where `‖c‖ ≤ C` and `‖a - a'‖ ≤ ε` (Cauchy–Schwarz);
* hence the *bookkeeping pair* a ledger needs — `0 ≤ del`, `del² ≤ ρ²σ`, and the separation
  clause — holds at `del := m + C·ε`.

The point of the sign: the displacement **inflates** the recorded margin (a displaced centre can
only weaken the guarantee), so the ledger must have room for `C·ε` on top of the oracle's own
margin. Recording `m - C·ε` would be unsound.
-/

open Finset

namespace QMCLeafB.SnapLedger

variable {k : ℕ}

/-- Euclidean norm on `Fin k → ℝ`, as a plain square root of a sum of squares. -/
noncomputable def norm2 (v : Fin k → ℝ) : ℝ := Real.sqrt (∑ i, (v i) ^ 2)

theorem norm2_nonneg (v : Fin k → ℝ) : 0 ≤ norm2 v := Real.sqrt_nonneg _

theorem norm2_sq (v : Fin k → ℝ) : norm2 v ^ 2 = ∑ i, (v i) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (v i))

/-- Cauchy–Schwarz for the plain dot product. -/
theorem abs_dot_le (c d : Fin k → ℝ) : |∑ i, c i * d i| ≤ norm2 c * norm2 d := by
  have hsq : (∑ i, c i * d i) ^ 2 ≤ (norm2 c * norm2 d) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin k)) c d
    rw [mul_pow, norm2_sq, norm2_sq]
    exact h
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (mul_nonneg (norm2_nonneg c) (norm2_nonneg d))] at h

/-- **Centre displacement versus margin.** A cut separating `S` around `a` with margin `m`
separates it around `a'` with the inflated margin `m + C·ε`. -/
theorem separates_of_displacement {S : Set (Fin k → ℝ)} {c a a' : Fin k → ℝ} {m C ε : ℝ}
    (hsep : ∀ z ∈ S, -m ≤ ∑ i, c i * (z i - a i))
    (hC : norm2 c ≤ C) (hε : norm2 (a - a') ≤ ε) :
    ∀ z ∈ S, -(m + C * ε) ≤ ∑ i, c i * (z i - a' i) := by
  intro z hz
  have hsplit : ∑ i, c i * (z i - a' i)
      = ∑ i, c i * (z i - a i) + ∑ i, c i * (a i - a' i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hC0 : 0 ≤ C := le_trans (norm2_nonneg c) hC
  have hsecond : -(C * ε) ≤ ∑ i, c i * (a i - a' i) := by
    have h := abs_dot_le c (a - a')
    have heq : ∑ i, c i * ((a - a') i) = ∑ i, c i * (a i - a' i) := by
      exact Finset.sum_congr rfl fun i _ => by simp
    rw [heq] at h
    have hle : |∑ i, c i * (a i - a' i)| ≤ C * ε :=
      h.trans (mul_le_mul hC hε (norm2_nonneg _) hC0)
    exact (abs_le.mp hle).1
  linarith [hsep z hz, hsecond, hsplit]

/-- **The ledger pair**: the snap-inflated margin is nonnegative, it fits the ledger's quadratic
room `del² ≤ ρ²σ`, and the cut separates the body around the recorded centre with that margin. -/
theorem ledger_round_ok {S : Set (Fin k → ℝ)} {c a a' : Fin k → ℝ} {m C ε rho sigma : ℝ}
    (hsep : ∀ z ∈ S, -m ≤ ∑ i, c i * (z i - a i))
    (hC : norm2 c ≤ C) (hε : norm2 (a - a') ≤ ε)
    (hm : 0 < m) (hε0 : 0 ≤ ε) (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hroom : (m + C * ε) ^ 2 ≤ rho ^ 2 * sigma) :
    0 ≤ m + C * ε ∧ (m + C * ε) ^ 2 ≤ rho ^ 2 * sigma ∧
      ∀ z ∈ S, -(m + C * ε) ≤ ∑ i, c i * (z i - a' i) := by
  have hC0 : 0 ≤ C := le_trans (norm2_nonneg c) hC
  have hdel0 : 0 ≤ m + C * ε := by nlinarith
  exact ⟨hdel0, hroom, separates_of_displacement hsep hC hε⟩

end QMCLeafB.SnapLedger

open QMCLeafB.SnapLedger

/-- **The platform node**: the margin–ledger joint in plain square-root form (no local
definitions), i.e. the statement a snapped-centre separation loop records per round. -/
theorem solution {k : ℕ} {S : Set (Fin k → ℝ)} {c a a' : Fin k → ℝ} {m C eps rho sigma : ℝ}
    (hsep : ∀ z ∈ S, -m ≤ ∑ i, c i * (z i - a i))
    (hC : Real.sqrt (∑ i, (c i) ^ 2) ≤ C)
    (heps : Real.sqrt (∑ i, (a i - a' i) ^ 2) ≤ eps)
    (hm : 0 < m) (heps0 : 0 ≤ eps) (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hroom : (m + C * eps) ^ 2 ≤ rho ^ 2 * sigma) :
    0 ≤ m + C * eps ∧ (m + C * eps) ^ 2 ≤ rho ^ 2 * sigma ∧
      ∀ z ∈ S, -(m + C * eps) ≤ ∑ i, c i * (z i - a' i) := by
  have hC' : QMCLeafB.SnapLedger.norm2 c ≤ C := by
    rw [QMCLeafB.SnapLedger.norm2]; exact hC
  have heps' : QMCLeafB.SnapLedger.norm2 (a - a') ≤ eps := by
    rw [QMCLeafB.SnapLedger.norm2]; exact heps
  exact QMCLeafB.SnapLedger.ledger_round_ok hsep hC' heps' hm heps0 hrho hsigma hroom
