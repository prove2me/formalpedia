-- Prove2me | Theorems.Thm_CostlyShort_OneAsset_prop3_eq30_iff_gQuad
-- name    : CostlyShort.OneAsset.prop3_eq30_iff_gQuad
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:32.256348+00:00
-- url     : https://prove2.me/theorems/fea7639f-5bb8-42ad-8f50-f675e92cda7b
-- title:
--   Proof of Proposition 3, p. 50 — on the shorting region, (30) is equivalent to g(γ) = 0
-- statement:
--   Let $\sigma>0$ and $s\in(0,1)$, and let $\Delta,\gamma\in\mathbb R$ be the belief gap and the lending yield per unit of volatility, so that the flow quantities are $\delta=\sigma\Delta$ and $\Gamma=\sigma\gamma$. Then the lending-yield equation (30) of the one-asset system, written on the shorting region (where its indicator equals one),
--   $$
--   \sigma\gamma=\frac{(1-s)(s\sigma\Delta-\sigma\gamma-\sigma^2)\big((\sigma\Delta+\sigma\gamma)s-\sigma^2\big)}{\sigma^2(1+s)^2},
--   $$
--   holds if and only if $g(\gamma)=0$, where
--   $$
--   g(\gamma)=(1-s)(s\Delta-\gamma-\sigma)\big((\gamma+\Delta)s-\sigma\big)-\gamma\sigma(1+s)^2 .
--   $$
--
--   This reduces the fixed-point equation for the lending yield to finding a root of a quadratic, which is the first step of the paper's proof of Proposition 3.
--
--   **Formalization Note** The paper states the equivalence "for $s_t>s^*$"; there (30) reads exactly as displayed above, which is what the Lean states. The equivalence is an algebraic identity and does not use $s>s^*$. In the one-asset case the volatility of the risky asset equals $\sigma$, so $\Gamma=\sigma\gamma$ and $\delta=\sigma\Delta$.
-- source:
--   Evgeniou, Hugonnier & Prieto, Asset Pricing with Costly Short Sales, SFI Research Paper N°22-21 (version of September 22, 2022), App. A, proof of Proposition 3, p. 50 (first sentence and the definition of g_t); (30), p. 27

import Mathlib
import Definitions.Def_CostlyShort_OneAsset_Setting

namespace CostlyShort.OneAsset

theorem prop3_eq30_iff_gQuad (σ s Δ γ : ℝ) (hσ : 0 < σ) (hs0 : 0 < s) (hs1 : s < 1) :
    (σ * γ = (1 - s) * (s * (σ * Δ) - σ * γ - σ ^ 2) * ((σ * Δ + σ * γ) * s - σ ^ 2)
        / (σ ^ 2 * (1 + s) ^ 2)) ↔ gQuad σ Δ s γ = 0 := by sorry

end CostlyShort.OneAsset
