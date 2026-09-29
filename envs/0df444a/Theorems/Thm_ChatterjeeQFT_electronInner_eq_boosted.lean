-- Prove2me | Theorems.Thm_ChatterjeeQFT_electronInner_eq_boosted
-- name    : ChatterjeeQFT.electronInner_eq_boosted
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:42:35.167822+00:00
-- url     : https://prove2.me/theorems/5ff69c83-f99b-4934-9742-aa777d2486ab
-- title:
--   The weighted electron inner product equals the plain $L^2$ inner product of $V_p^{-1}\psi$
-- statement:
--   The weighted inner product of the electron space can be rewritten as an unweighted
--   one after applying the inverse boost pointwise: for all $\mathbb{C}^2$-valued $\psi, \varphi$,
--
--   $$\int_{X_m} \psi(p)^{\dagger} V_p^{-2} \varphi(p)\, d\lambda_m(p)
--   \;=\; \int_{X_m} \big(V_p^{-1}\psi(p)\big)^{\dagger}\big(V_p^{-1}\varphi(p)\big)\, d\lambda_m(p),$$
--
--   which holds pointwise in $p$ because $V_p$ is Hermitian. This identifies the electron space
--   $L^2(X_m, d\lambda_m, \mathbb{C}^2)$ with the ordinary $\mathbb{C}^2$-valued $L^2$ space of
--   $\lambda_m$ via the measurable field of isomorphisms $\psi \mapsto V_{\cdot}^{-1}\psi$, and is the
--   route by which the source's assertion that "$H$ is indeed a Hilbert space under this inner
--   product" — positive definiteness and completeness — is obtained.
-- source:
--   S. Chatterjee, *Lectures on Quantum Field Theory* (Stanford, 2018-19, combined scribed lecture notes), https://souravchatterjee.su.domains/qft-lectures-combined.pdf, Lecture 25 §25.3, pp. 108-109 ("It is not difficult to verify that $H$ is indeed a Hilbert space under this inner product").

import Mathlib
import Definitions.Def_ChatterjeeQFT_ElectronSpace
open MeasureTheory Matrix
open scoped ENNReal ComplexOrder

namespace ChatterjeeQFT

theorem electronInner_eq_boosted (m : ℝ) (hm : 0 < m) (ψ φ : (Fin 4 → ℝ) → (Fin 2 → ℂ)) :
    electronInner m ψ φ
      = ∫ p, ∑ i : Fin 2, (starRingEnd ℂ) (((pureBoost m p)⁻¹ *ᵥ ψ p) i) *
          (((pureBoost m p)⁻¹ *ᵥ φ p) i) ∂(massShellMeasure m) := by sorry

end ChatterjeeQFT
