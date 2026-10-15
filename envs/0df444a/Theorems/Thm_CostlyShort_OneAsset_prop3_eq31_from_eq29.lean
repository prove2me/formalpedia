-- Prove2me | Theorems.Thm_CostlyShort_OneAsset_prop3_eq31_from_eq29
-- name    : CostlyShort.OneAsset.prop3_eq31_from_eq29
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:36.845874+00:00
-- url     : https://prove2.me/theorems/9281c69c-1fbd-4996-b864-ae1a83555d26
-- title:
--   Proof of Proposition 3, p. 50 — substituting (32) into (29) gives (31)
-- statement:
--   Let $\sigma>0$, $s\in(0,1)$ and $\delta\in\mathbb R$ with $\sigma^2<s\delta$ (the shorting region $s>s^*$). Let $\Phi=\Phi(\sigma,\delta,s)$ be the closed-form shorting cost (31) and $\Gamma=\Gamma(\sigma,\delta,s)$ the closed-form lending yield (32). Then the shorting-cost equation (29) holds on the region:
--   $$
--   \Phi=\frac{(\delta+\Gamma)s-\sigma^2}{1+s}.
--   $$
--
--   With the previous milestone, this shows that $(\Phi,\Gamma)$ given by (31)–(32) solves the whole system (29)–(30) on the shorting region.
--
--   **Formalization Note** On the region both indicators equal one; the Lean uses the definitions `costOne` and `yieldOne` of (31) and (32), whose common guard $\sigma^2<s\delta$ is the hypothesis.
-- source:
--   Evgeniou, Hugonnier & Prieto, Asset Pricing with Costly Short Sales, SFI Research Paper N°22-21 (version of September 22, 2022), App. A, proof of Proposition 3, p. 50 ("substituting into (29) gives (31)"); (29), (31), p. 27

import Mathlib
import Definitions.Def_CostlyShort_OneAsset_Setting

namespace CostlyShort.OneAsset

theorem prop3_eq31_from_eq29 (σ δ s : ℝ) (hσ : 0 < σ) (hs0 : 0 < s) (hs1 : s < 1)
    (hreg : σ ^ 2 < s * δ) :
    costOne σ δ s = ((δ + yieldOne σ δ s) * s - σ ^ 2) / (1 + s) := by sorry

end CostlyShort.OneAsset
