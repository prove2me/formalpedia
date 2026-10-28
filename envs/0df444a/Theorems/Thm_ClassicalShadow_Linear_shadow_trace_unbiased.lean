-- Prove2me | Theorems.Thm_ClassicalShadow_Linear_shadow_trace_unbiased
-- name    : ClassicalShadow.Linear.shadow_trace_unbiased
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:45.204979+00:00
-- url     : https://prove2.me/theorems/82f9a2c4-5b6e-4778-bd2e-a7395d0e1f2f
-- title:
--   p. 11, after (S3) — classical shadows have unit trace and E[ρ̂] = ρ
-- statement:
--   Let $\mathcal U = \{(w_i, U_i)\}$ be a finite, tomographically complete measurement primitive on $n$ qubits and $\rho$ a density operator. For the outcome $\omega = (i,b)$ write $\hat\rho_\omega = \mathcal M^{-1}(U_i^\dagger|b\rangle\langle b|U_i)$ for its classical shadow and $p_\rho(\omega) = w_i\langle b|U_i\rho U_i^\dagger|b\rangle$ for its probability. Then
--
--   1. every classical shadow has unit trace, $\operatorname{tr}(\hat\rho_\omega) = 1$ for all $\omega$;
--   2. the shadow reproduces the state in expectation:
--   $$\mathbb E[\hat\rho] = \sum_{\omega} p_\rho(\omega)\, \hat\rho_\omega = \rho .$$
--
--   Unbiasedness is the reason the shadow can replace the unknown state in any linear prediction, and unit trace is what lets the variance depend only on the traceless part of an observable.
-- source:
--   Huang, Kueng, Preskill, Predicting many properties of a quantum system from very few measurements, arXiv:2002.08953v2, p. 11, paragraph after (S3)

import Mathlib
import Definitions.Def_ClassicalShadow_Linear_Setting

namespace ClassicalShadow.Linear
theorem shadow_trace_unbiased {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι)
    (hE : TomographicallyComplete E) (ρ : Op n) (hρ : WildeQIT.IsDensityOperator ρ) :
    (∀ ω : ι × Bits n, (shadow E ω).trace = 1) ∧
      ∑ ω : ι × Bits n, ((snapProb E ρ ω : ℝ) : ℂ) • shadow E ω = ρ := by sorry
end ClassicalShadow.Linear
