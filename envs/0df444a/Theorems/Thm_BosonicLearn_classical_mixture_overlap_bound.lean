-- Prove2me | Theorems.Thm_BosonicLearn_classical_mixture_overlap_bound
-- name    : BosonicLearn.classical_mixture_overlap_bound
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T21:30:38.722217+00:00
-- url     : https://prove2.me/theorems/62edf1bf-a413-4bd9-bb5e-b980daba808d
-- title:
--   Classical states are as close as their mixing measures overlap: $\tfrac12\|\sigma'-\sigma\|_1\le1-\kappa(\mathbb R^{2n})$ for $\kappa\le\gamma,\gamma'$
-- statement:
--   Data processing for classical states (mixtures of coherent states).
--
--   Let $\gamma,\gamma'$ be probability measures on phase space $\mathbb R^{2n}$ and $\sigma=\int|\alpha(x)\rangle\langle\alpha(x)|\,d\gamma(x)$, $\sigma'=\int|\alpha(x)\rangle\langle\alpha(x)|\,d\gamma'(x)$ the corresponding mixtures of coherent states, specified through their characteristic functions $\chi_\sigma(\xi)=\hat\gamma(\xi)\,e^{-|\xi|^2/4}$, $\chi_{\sigma'}(\xi)=\hat\gamma'(\xi)\,e^{-|\xi|^2/4}$. If a measure $\kappa$ satisfies $\kappa\le\gamma$ and $\kappa\le\gamma'$, then
--
--   $$
--   \tfrac12\|\sigma'-\sigma\|_1\ \le\ 1-\kappa(\mathbb R^{2n}).
--   $$
--
--   With $\kappa=\gamma\wedge\gamma'$ the right-hand side is the total variation distance of $\gamma$ and $\gamma'$.
--
--   Role. Used with `BosonicLearn.gaussian_shift_overlap` in `BosonicLearn.lemma_18_classical`.
--
--   **Formalization Note** $\gamma,\gamma'$ are probability measures on `EuclideanSpace ℝ (Fin n × Fin 2)` (interleaved quadrature coordinates), $\hat\gamma$ is Mathlib's `charFun`, and a state is identified with the mixture through `BosonicLearn.state_ext_characteristic`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 18 (first-moment perturbation), Eq. (204), p. 60; proof of Theorem 8, p. 62

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Two classical states are as close as their mixing measures overlap.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 18, p. 60, and the proof of Theorem 8, p. 62 (data processing for classical mixtures of coherent states).

Let `σ, σ'` be the mixtures of coherent states over probability measures `γ, γ'` on phase space
(`χ_σ(ξ) = γ̂(ξ) e^{−|ξ|²/4}`, `χ_{σ'}(ξ) = γ̂'(ξ) e^{−|ξ|²/4}`). If a measure `κ` satisfies `κ ≤ γ` and `κ ≤ γ'`, then
`½‖σ' − σ‖₁ ≤ 1 − κ(ℝ²ⁿ)`. (With `κ = γ ∧ γ'` the right-hand side is the total variation distance of `γ, γ'`.)

**Formalization Note.** `γ, γ'` are probability measures on `EuclideanSpace ℝ (Fin n × Fin 2)` and `γ̂` is `charFun`. -/
theorem classical_mixture_overlap_bound {n : ℕ} (γ γ' κ : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))
    [IsProbabilityMeasure γ] [IsProbabilityMeasure γ'] (hκ : κ ≤ γ) (hκ' : κ ≤ γ')
    (σ σ' : State (Occupation (Fin n)))
    (hσ : ∀ ξ : Fin n × Fin 2 → ℝ, oscillatorCharacteristic σ.coefficients ξ =
      charFun γ (WithLp.toLp 2 ξ) * ((Real.exp (-(∑ a, ξ a ^ 2) / 4) : ℝ) : ℂ))
    (hσ' : ∀ ξ : Fin n × Fin 2 → ℝ, oscillatorCharacteristic σ'.coefficients ξ =
      charFun γ' (WithLp.toLp 2 ξ) * ((Real.exp (-(∑ a, ξ a ^ 2) / 4) : ℝ) : ℂ)) :
    traceDist σ'.coefficients σ.coefficients ≤ ENNReal.ofReal (1 - (κ Set.univ).toReal) := by sorry

end BosonicLearn
