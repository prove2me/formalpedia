-- Prove2me | Theorems.Thm_DynamicAssortment_Separation_display12_optimal_assortment_stable
-- name    : DynamicAssortment.Separation.display12_optimal_assortment_stable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:12:27.414576+00:00
-- url     : https://prove2.me/theorems/3e1b3867-431d-4ffd-9aa1-0f36a7326149
-- title:
--   Display (12) (p. 402) — if ‖μ − μ̂‖ on S*(μ) ∪ S*(μ̂) is below (2‖w‖_∞KC)⁻¹δ(μ)r(S*(μ), μ), then S*(μ̂) = S*(μ)
-- statement:
--   Let $1\le C\le N$, $w_i>0$, $f$ a positive noise density, and $S^*$ an optimal-assortment selection whose optimum at $\mu$ is unique. Let $K>0$ be such that every $p(S,\cdot)$, $S\in\mathcal S$, is $K$-Lipschitz in the sup norm. Let $\delta(\mu)$ be the minimum relative optimality gap. Then for every mean-utility vector $\nu$,
--   $$\|\mu-\nu\|_{S^*(\mu)\cup S^*(\nu)}<(2\|w\|_\infty KC)^{-1}\,\delta(\mu)\,r(S^*(\mu),\mu)\ \Longrightarrow\ S^*(\nu)=S^*(\mu).$$
--   Equivalently, $\{S^*(\mu)\ne S^*(\hat\mu_t)\}\subseteq\{\|\mu-\hat\mu_t\|_{S^*(\mu)\cup S^*(\hat\mu_t)}\ge(2\|w\|_\infty KC)^{-1}\delta(\mu)r(S^*(\mu),\mu)\}$, which is relation (12).
--
--   If the estimated mean utilities are uniformly close to the true ones, solving the single-sale problem with the estimates returns the true optimal assortment.
--
--   **Formalization Note** $\delta(\mu)=\min_{S\in\mathcal S,\,S\neq S^*(\mu)}\big(r(S^*(\mu),\mu)-r(S,\mu)\big)/r(S^*(\mu),\mu)$ is defined locally (`optimalityGap`), because the paper's definition, (13), is in its online companion. The statement is deterministic and holds for every $\nu$.
-- source:
--   Sauré, Zeevi, Optimal Dynamic Assortment Planning with Demand Learning, Manuf. Serv. Oper. Manag. 15(3), 2013, p. 402, App. A, proof of Theorem 2, Step 2, display (12) and the implication preceding it

import Mathlib
import Definitions.Def_DynamicAssortment_Separation_ChoiceModel

namespace DynamicAssortment.Separation

/-- Display (12) (App. A, Step 2, p. 402): with `K` as in (11) and `δ(μ)` the minimum relative
optimality gap, if `‖μ - ν‖_{S*(μ) ∪ S*(ν)} < (2 ‖w‖_∞ K C)⁻¹ δ(μ) r(S*(μ), μ)` then
`S*(ν) = S*(μ)`. -/
theorem display12_optimal_assortment_stable {N C : ℕ} (hC : 1 ≤ C) (hCN : C ≤ N)
    (f : ℝ → ℝ) (hf : IsNoiseDensity f) (w : Fin N → ℝ) (hw : ∀ i, 0 < w i)
    (μ : Fin N → ℝ) (opt : (Fin N → ℝ) → Finset (Fin N))
    (hopt : IsOptimalSelection f w C opt) (huniq : UniqueOptimum f w C μ (opt μ))
    (K : NNReal) (hK : 0 < K)
    (hlip : ∀ S ∈ assortments N C,
      LipschitzWith K (fun ν : Fin N → ℝ => fun i => choiceProb f ν S i)) :
    ∀ ν : Fin N → ℝ,
      normOn (opt μ ∪ opt ν) (μ - ν) <
          (2 * normOn Finset.univ w * K * C)⁻¹ * optimalityGap f w C μ (opt μ) *
            profit f w μ (opt μ) →
        opt ν = opt μ := by sorry

end DynamicAssortment.Separation
