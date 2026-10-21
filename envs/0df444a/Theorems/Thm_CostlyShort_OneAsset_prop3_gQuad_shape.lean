-- Prove2me | Theorems.Thm_CostlyShort_OneAsset_prop3_gQuad_shape
-- name    : CostlyShort.OneAsset.prop3_gQuad_shape
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:40.200461+00:00
-- url     : https://prove2.me/theorems/1408de5d-d0f7-48c4-8bad-026c65dad78a
-- title:
--   Proof of Proposition 3, p. 50 — g(0) > 0, g′(0) < 0, g″ = −2s(1−s) < 0 and g(γ) → −∞
-- statement:
--   Let $\sigma>0$, $s\in(0,1)$ and $\Delta\in\mathbb R$ with $\sigma<s\Delta$ (the shorting region $s>s^*$ in units per unit of volatility), and let
--   $$
--   g(\gamma)=(1-s)(s\Delta-\gamma-\sigma)\big((\gamma+\Delta)s-\sigma\big)-\gamma\sigma(1+s)^2 .
--   $$
--   Then
--   1. $g(0)=(1-s)(s\Delta-\sigma)^2>0$;
--   2. $g'(0)=-\sigma(1+s)^2-(1-s)^2(s\Delta-\sigma)<0$;
--   3. $g''(\gamma)=-2s(1-s)$ for every $\gamma$;
--   4. $g(\gamma)\to-\infty$ as $\gamma\to\infty$.
--
--   These four facts describe a concave quadratic that is positive at the origin, and they are what the paper uses to conclude that $g$ has exactly one strictly positive root.
--
--   **Formalization Note** The paper prints $g''_t(\gamma)=-s_t(1-s_t)<0$; differentiating the displayed $g_t$ twice gives $-2s_t(1-s_t)$, which is what the Lean states. The sign, the only thing the proof uses, is the same. Derivatives are Mathlib's `deriv` of the function $\gamma\mapsto g(\gamma)$.
-- source:
--   Evgeniou, Hugonnier & Prieto, Asset Pricing with Costly Short Sales, SFI Research Paper N°22-21 (version of September 22, 2022), App. A, proof of Proposition 3, p. 50 (the four displays after "Since")

import Mathlib
import Definitions.Def_CostlyShort_OneAsset_Setting

open Filter

namespace CostlyShort.OneAsset

theorem prop3_gQuad_shape (σ s Δ : ℝ) (hσ : 0 < σ) (hs0 : 0 < s) (hs1 : s < 1)
    (hreg : σ < s * Δ) :
    (gQuad σ Δ s 0 = (1 - s) * (s * Δ - σ) ^ 2 ∧ 0 < gQuad σ Δ s 0) ∧
    (deriv (gQuad σ Δ s) 0 = -σ * (1 + s) ^ 2 - (1 - s) ^ 2 * (s * Δ - σ) ∧
      deriv (gQuad σ Δ s) 0 < 0) ∧
    (∀ γ : ℝ, deriv (deriv (gQuad σ Δ s)) γ = -2 * s * (1 - s)) ∧
    Tendsto (gQuad σ Δ s) atTop atBot := by sorry

end CostlyShort.OneAsset
