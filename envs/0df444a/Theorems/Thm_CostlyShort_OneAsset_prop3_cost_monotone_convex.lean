-- Prove2me | Theorems.Thm_CostlyShort_OneAsset_prop3_cost_monotone_convex
-- name    : CostlyShort.OneAsset.prop3_cost_monotone_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:33.065365+00:00
-- url     : https://prove2.me/theorems/2307edbd-55b9-42ba-8b5d-ece110c2ddc4
-- title:
--   Proposition 3, pp. 27–28 — the shorting cost (31) is increasing and convex in δ
-- statement:
--   Let $\sigma>0$ and $s\in(0,1)$, and consider the closed-form shorting cost (31) as a function of the belief gap $\delta\ge 0$,
--   $$
--   \delta\mapsto\Phi(\sigma,\delta,s)=\mathbb 1_{\{\sigma^2<s\delta\}}\,\frac{s(1-s)\delta-2\sigma^2+\sqrt{s^2(1-s)^2\delta^2+4\sigma^4 s}}{2(1-s)} .
--   $$
--   Then
--   1. $\delta\mapsto\Phi(\sigma,\delta,s)$ is non-decreasing on $[0,\infty)$;
--   2. it is strictly increasing on the shorting region $\delta>\sigma^2/s$;
--   3. it is convex on $[0,\infty)$.
--
--   This is the shorting-cost half of the last clause of Proposition 3, "both are increasing and convex in $\delta$": a larger disagreement makes short selling more expensive, at an increasing rate.
--
--   **Formalization Note** $\Phi$ vanishes for $\delta\le\sigma^2/s$ (outside the shorting region), so "increasing" is read as non-decreasing on $[0,\infty)$ together with strict increase on $(\sigma^2/s,\infty)$. Convexity is stated on all of $[0,\infty)$, across the kink at $\delta=\sigma^2/s$.
-- source:
--   Evgeniou, Hugonnier & Prieto, Asset Pricing with Costly Short Sales, SFI Research Paper N°22-21 (version of September 22, 2022), Proposition 3, pp. 27–28 ("and both are increasing and convex in δ"); App. A, proof of Proposition 3, p. 50

import Mathlib
import Definitions.Def_CostlyShort_OneAsset_Setting

namespace CostlyShort.OneAsset

theorem prop3_cost_monotone_convex (σ s : ℝ) (hσ : 0 < σ) (hs0 : 0 < s) (hs1 : s < 1) :
    MonotoneOn (fun δ => costOne σ δ s) (Set.Ici 0) ∧
    StrictMonoOn (fun δ => costOne σ δ s) (Set.Ioi (σ ^ 2 / s)) ∧
    ConvexOn ℝ (Set.Ici 0) (fun δ => costOne σ δ s) := by sorry

end CostlyShort.OneAsset
