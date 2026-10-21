-- Prove2me | Theorems.Thm_CostlyShort_OneAsset_prop3_eq32_solves_eq30
-- name    : CostlyShort.OneAsset.prop3_eq32_solves_eq30
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:28.279575+00:00
-- url     : https://prove2.me/theorems/00a23501-49ca-4873-9272-17b96cd91ffb
-- title:
--   Proof of Proposition 3, p. 50 — the closed form (32) is a strictly positive solution of (30)
-- statement:
--   Let $\sigma>0$, $s\in(0,1)$ and $\delta\in\mathbb R$ with $\sigma^2<s\delta$ (the shorting region $s>s^*$). Write $\Gamma=\Gamma(\sigma,\delta,s)$ for the closed-form lending yield (32),
--   $$
--   \Gamma=\frac{-s\big((1-s)^2\delta+4\sigma^2\big)+(1+s)\sqrt{s^2(1-s)^2\delta^2+4\sigma^4 s}}{2s(1-s)} .
--   $$
--   Then $\Gamma>0$ and $\Gamma$ solves the lending-yield equation (30) on the shorting region:
--   $$
--   \Gamma=\frac{(1-s)(s\delta-\Gamma-\sigma^2)\big((\delta+\Gamma)s-\sigma^2\big)}{\sigma^2(1+s)^2}.
--   $$
--
--   This is the "direct calculation" of the paper identifying the unique positive root of the quadratic with the explicit formula (32).
--
--   **Formalization Note** On the region the indicator in (32) equals one, so $\Gamma$ is the displayed fraction; the Lean uses the definition `yieldOne` of (32), whose guard $\sigma^2<s\delta$ is the hypothesis.
-- source:
--   Evgeniou, Hugonnier & Prieto, Asset Pricing with Costly Short Sales, SFI Research Paper N°22-21 (version of September 22, 2022), App. A, proof of Proposition 3, p. 50 ("A direct calculation shows that this solution is given by (32)"); (30) and (32), p. 27

import Mathlib
import Definitions.Def_CostlyShort_OneAsset_Setting

namespace CostlyShort.OneAsset

theorem prop3_eq32_solves_eq30 (σ δ s : ℝ) (hσ : 0 < σ) (hs0 : 0 < s) (hs1 : s < 1)
    (hreg : σ ^ 2 < s * δ) :
    0 < yieldOne σ δ s ∧
    yieldOne σ δ s = (1 - s) * (s * δ - yieldOne σ δ s - σ ^ 2) * ((δ + yieldOne σ δ s) * s - σ ^ 2)
      / (σ ^ 2 * (1 + s) ^ 2) := by sorry

end CostlyShort.OneAsset
