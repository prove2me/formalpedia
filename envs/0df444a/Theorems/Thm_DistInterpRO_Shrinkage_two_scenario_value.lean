-- Prove2me | Theorems.Thm_DistInterpRO_Shrinkage_two_scenario_value
-- name    : DistInterpRO.Shrinkage.two_scenario_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:53:52.008969+00:00
-- url     : https://prove2.me/theorems/95a6e946-c033-4774-bada-e817f65bb56a
-- title:
--   §4.2, proof of Theorem 4.1 — the two-scenario DRSP value equals (1 − α)f(v, x₀) + α·min over Δ (Corollary 5.2)
-- statement:
--   Let $f(v,\cdot):\mathbb{R}^m\to\mathbb{R}$ be continuous, $\Delta\subseteq\mathbb{R}^m$ compact with $0\in\Delta$, $x_0\in\mathbb{R}^m$ and $\alpha\in(0,1)$. With $\hat{\mathcal P}'=\{\mu\in\mathcal P\mid\mu(\{x_0\})\ge1-\alpha,\ \mu(x_0+\Delta)=1\}$,
--   $$(1-\alpha)f(v,x_0)+\alpha\min_{x_\delta\in\Delta}f(v,x_0+x_\delta)=\inf_{\mu\in\hat{\mathcal P}'}\int_{\mathbb{R}^m}f(v,x)\,d\mu(x).$$
--
--   The paper derives this equality from its Corollary 5.2 (p. 107) with two nested sets $\mathcal Z_1=\{x_0\}\subseteq\mathcal Z_2=x_0+\Delta$ and masses $p_1=1-\alpha$, $p_2=1$. It identifies the value of the two-scenario distributionally robust problem, which is the bridge between the shrinkage bounds and the DRSP formulation.
--
--   **Formalization Note** The minimum is a real infimum over the subtype of $\Delta$ (attained by compactness and continuity), and the right side is `drspValue`, a real infimum over the subtype of $\hat{\mathcal P}'$ of Bochner integrals. The hypothesis $0\in\Delta$ (the nesting $\mathcal Z_1\subseteq\mathcal Z_2$) is implicit on the page; without it $\hat{\mathcal P}'$ is empty. Continuity and compactness make every integral finite.
-- source:
--   Xu, Caramanis and Mannor, A Distributional Interpretation of Robust Optimization, Math. Oper. Res. 37(1) (2012), p. 105, §4.2, proof of Theorem 4.1, last display ("implied by Corollary 5.2"); Corollary 5.2 on p. 107

import Mathlib
import Definitions.Def_DistInterpRO_Shrinkage_Model

open MeasureTheory
open scoped Pointwise

namespace DistInterpRO.Shrinkage

/-- §4.2, proof of Theorem 4.1 (p. 105), last display, "implied by Corollary 5.2":
`(1 − α)f(v, x₀) + α min_{x_δ∈Δ} f(v, x₀ + x_δ) = inf_{μ∈𝒫̂′} ∫ f(v, x) dμ(x)`,
with `𝒫̂′ = {μ ∈ 𝒫 | μ({x₀}) ≥ 1 − α, μ(x₀ + Δ) = 1}`. -/
theorem two_scenario_value {m : ℕ} {V : Type*} (f : V → EuclideanSpace ℝ (Fin m) → ℝ) (v : V)
    (hf : Continuous (f v))
    (x₀ : EuclideanSpace ℝ (Fin m)) (Δ : Set (EuclideanSpace ℝ (Fin m))) (hΔc : IsCompact Δ)
    (hΔ0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ Δ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    (1 - α) * f v x₀ + α * (⨅ x : Δ, f v (x₀ + x)) = drspValue (f v) x₀ Δ (1 - α) := by sorry

end DistInterpRO.Shrinkage
