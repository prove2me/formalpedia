-- Prove2me | Theorems.Thm_BosonicLearn_fugacity_characteristic
-- name    : BosonicLearn.fugacity_characteristic
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T19:44:53.696296+00:00
-- url     : https://prove2.me/theorems/7de673e8-3297-4ace-a186-9561507f1b58
-- title:
--   Characteristic function of $\det(I-R)\Gamma(R)$: $\mathrm{Tr}(\rho_Re^{i\xi\cdot\hat r})=\exp(-\tfrac12\zeta^\dagger(1+R)(1-R)^{-1}\zeta)$
-- statement:
--   The Weyl characteristic function of the passive Gaussian state with fugacity matrix $R$.
--
--   Let $R$ be a positive semidefinite $n\times n$ complex matrix with $1-R$ positive definite, and $\rho_R=\det(1-R)\Gamma(R)$. For $\xi\in\mathbb R^{2n}$ put $\zeta_j=(-\xi_{p_j}+i\xi_{q_j})/\sqrt2$, so that $e^{i\xi\cdot\hat r}=D(\zeta)$. Then the iterated series defining $\operatorname{Tr}(\rho_Re^{i\xi\cdot\hat r})$ converge and
--
--   $$
--   \operatorname{Tr}\big(\rho_R\,e^{i\xi\cdot\hat r}\big)=\exp\!\Big(-\tfrac12\,\zeta^\dagger(1+R)(1-R)^{-1}\zeta\Big).
--   $$
--
--   Role. This is the computation behind clause 1 of Lemma 2 of the paper: $\rho_R$ is Gaussian, with covariance read off from $(1+R)(1-R)^{-1}$ (`BosonicLearn.fugacity_isGaussianState`).
--
--   **Formalization Note** The left-hand side is the published `Support50.P14.oscillatorCharacteristic` ($\sum_u\sum_v\rho_{uv}W(\xi)_{vu}$ with interleaved quadrature index $(j,0)=q_j$, $(j,1)=p_j$), and the convergence statement is `OscillatorCharacteristicSummable`. The quadratic form is written as the double sum $\sum_{j,k}\bar\zeta_j\,((1+R)(1-R)^{-1})_{jk}\,\zeta_k$.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 2 and Eq. (21), p. 20 (passive Gaussian states as det(I − R)Γ(R)); §1.1, Eqs. (2) and (4), pp. 4–5 (Gaussian states, characteristic function, passive Gaussian states)

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14 (oscillatorCharacteristic OscillatorCharacteristicSummable)
open scoped Matrix ComplexOrder

namespace BosonicLearn

/-- **Characteristic function of `det(I − R)Γ(R)`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 2, Eq. (21), p. 20: "the corresponding passive Gaussian state is ρ = det(I − R)Γ(R)"; §1.1, Eq. (2), pp. 4–5
(characteristic function of a Gaussian state).

Let `R` be positive semidefinite with `1 − R` positive definite and `ρ_R = det(1 − R)Γ(R)`. For `ξ ∈ ℝ^{2n}` let
`ζⱼ = (−ξ_{pⱼ} + i ξ_{qⱼ})/√2`, so that the Weyl operator is `e^{iξ·r̂} = D(ζ)`. Then

`Tr(ρ_R e^{iξ·r̂}) = exp(−½ ζ† (1 + R)(1 − R)⁻¹ ζ)`,

and the iterated sums defining the left-hand side converge.

**Formalization Note.** The left-hand side is the published `Support50.P14.oscillatorCharacteristic`
(`∑ᵤ ∑ᵥ ρ_{uv} W(ξ)_{vu}`, interleaved quadrature index `(j, 0) = qⱼ`, `(j, 1) = pⱼ`), and the convergence statement
is `OscillatorCharacteristicSummable`. -/
theorem fugacity_characteristic {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosDef) :
    OscillatorCharacteristicSummable (fugacityCoeff R) ∧
    ∀ ξ : Fin n × Fin 2 → ℝ,
      oscillatorCharacteristic (fugacityCoeff R) ξ =
        Complex.exp (-(1 / 2 : ℂ) *
          ∑ j, ∑ k, star ((-(ξ (j, 1) : ℂ) + Complex.I * (ξ (j, 0) : ℂ)) / (Real.sqrt 2 : ℂ)) *
            ((1 + R) * (1 - R)⁻¹) j k *
            ((-(ξ (k, 1) : ℂ) + Complex.I * (ξ (k, 0) : ℂ)) / (Real.sqrt 2 : ℂ))) := by sorry

end BosonicLearn
