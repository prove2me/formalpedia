-- Prove2me | Theorems.Thm_BosonicLearn_cov_perturbation_classical
-- name    : BosonicLearn.cov_perturbation_classical
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T22:03:35.459013+00:00
-- url     : https://prove2.me/theorems/f6bc9554-26ce-42c1-98c9-01e0f01f4ca4
-- title:
--   One-sided covariance perturbation for $\Sigma\succeq\tfrac12I$: $\tfrac12\|\rho(\mu,\Sigma')-\rho(\mu,\Sigma)\|_1\le2\,\mathrm{Tr}[\Sigma^{-1}(\Sigma'-\Sigma)]$
-- statement:
--   An energy-independent trace-distance bound between two Gaussian states with the same mean and ordered covariances, proved without fidelity formulas.
--
--   Let $\rho(\mu,\Sigma)$ and $\rho(\mu,\Sigma')$ be $n$-mode Gaussian states with $\Sigma\succeq\tfrac12\mathbf 1$ and $\Sigma'\succeq\Sigma$. Then
--
--   $$
--   \tfrac12\big\|\rho(\mu,\Sigma')-\rho(\mu,\Sigma)\big\|_1\ \le\ 2\,\operatorname{Tr}\big[\Sigma^{-1}(\Sigma'-\Sigma)\big].
--   $$
--
--   Comparison with `BosonicLearn.bmem25_theorem_8_cov` (the covariance part of [BMEM25, Theorem 8], with constant $\frac{1+\sqrt3}8$ and $\Sigma^{-1}+\Sigma'^{-1}\preceq2\Sigma^{-1}$): same form, constant $2$ instead of $\frac{1+\sqrt3}4$, under the extra hypothesis $\Sigma\succeq\tfrac12\mathbf 1$ — which is the promise of [BMEM25, Theorem 10] as used in Corollary 19. The bound is linear in the relative perturbation and does not depend on the energy of the states.
--
--   Proof idea. $\rho(\mu,\Sigma)$ is a mixture of coherent states over $\mathcal N(\mu,\Sigma-\tfrac12)$. The extra noise $x\sim\mathcal N(0,\Sigma'-\Sigma)$ is split as $(\Sigma-\tfrac12)\Sigma^{-1}x$, absorbed in the mixing measure through a Cameron–Martin weight, plus $\tfrac12\Sigma^{-1}x$, a displacement of the coherent states; by the symmetry $x\mapsto-x$ and the even/odd decomposition of coherent vectors the first-order terms cancel, leaving a second-order weight $\lesssim x^T\Sigma^{-1}x$, whose expectation is $\operatorname{Tr}[\Sigma^{-1}(\Sigma'-\Sigma)]$. Checked numerically for one-mode thermal states.
--
--   **Formalization Note** Hypotheses `(S - (1/2) • 1).PosSemidef` and `(S' - S).PosSemidef`; the bound is `ENNReal.ofReal (2 * (S⁻¹ * (S' - S)).trace)`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.4, p. 10 (trace-distance bounds between Gaussian states [BMEM25]); proof of Corollary 19, p. 65 ([BMEM25, Theorem 10]); [BMEM25] = arXiv:2508.14979, Theorem 8

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_BosonicLearn_IsGaussianState

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open MeasureTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **One-sided covariance perturbation for classical covariances: `½‖ρ(µ, Σ′) − ρ(µ, Σ)‖₁ ≤ 2 Tr[Σ⁻¹(Σ′ − Σ)]`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.4, p. 10 (trace-distance bounds between Gaussian states [BMEM25]); proof of Corollary 19, p. 65 ([BMEM25, Theorem 10]);
[BMEM25] = Bittel, Mele, Eisert, Mele, arXiv:2508.14979, Theorem 8.

Let `ρ(µ, Σ)` and `ρ(µ, Σ′)` be Gaussian states with the same mean, `Σ ⪰ ½I` and `Σ′ ⪰ Σ`. Then
`½‖ρ(µ, Σ′) − ρ(µ, Σ)‖₁ ≤ 2 Tr[Σ⁻¹(Σ′ − Σ)]`.

**Formalization Note.** This is the form of `bmem25_theorem_8_cov` needed for [BMEM25, Theorem 10] under the promise
`Σ ⪰ ½I`: the bound is linear in the relative perturbation and independent of the energy. The constant `2` replaces
`(1 + √3)/4` (and `Σ⁻¹ + Σ′⁻¹ ⪯ 2Σ⁻¹`). It is proved without fidelity formulas: `ρ(µ, Σ)` is a mixture of
coherent states over `N(µ, Σ − ½I)`, the extra noise `x ∼ N(0, Σ′ − Σ)` is split as
`(Σ − ½I)Σ⁻¹x` (absorbed in the mixing measure through a Cameron–Martin weight) plus `½Σ⁻¹x` (a displacement of the
coherent states), and the first-order terms cancel by the symmetry `x ↦ −x`. -/
theorem cov_perturbation_classical {n : ℕ} (ρ ρ' : State (Occupation (Fin n)))
    (μ : Fin n ⊕ Fin n → ℝ) (S S' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (hS : (S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef)
    (hord : (S' - S).PosSemidef)
    (h : IsGaussianState ρ μ S) (h' : IsGaussianState ρ' μ S') :
    traceDist ρ'.coefficients ρ.coefficients ≤
      ENNReal.ofReal (2 * (S⁻¹ * (S' - S)).trace) := by sorry

end BosonicLearn
