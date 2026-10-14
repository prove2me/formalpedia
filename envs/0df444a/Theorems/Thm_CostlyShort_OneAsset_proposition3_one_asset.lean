-- Prove2me | Theorems.Thm_CostlyShort_OneAsset_proposition3_one_asset
-- name    : CostlyShort.OneAsset.proposition3_one_asset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:28.736857+00:00
-- url     : https://prove2.me/theorems/2fd91d22-f8c2-462c-917d-826e6e64a5ae
-- title:
--   Proposition 3, pp. 27–28 — with one risky asset, (31)–(32) are the equilibrium cost and yield, increasing and convex in δ
-- statement:
--   **Proposition 3.** Consider the economy with a single risky asset, aggregate-consumption volatility $\sigma>0$ and optimist's consumption share $s\in(0,1)$, and let $s^*=\min\{1,\sigma^2/\delta\}$. For a belief gap $\delta\ge 0$, a shorting cost $\Phi$ and a lending yield $\Gamma\ge 0$ satisfy the equilibrium system
--   $$
--   \Phi=\mathbb 1_{\{s>s^*\}}\frac{(\delta+\Gamma)s-\sigma^2}{1+s},\qquad
--   \Gamma=\mathbb 1_{\{s>s^*\}}\frac{(1-s)(s\delta-\Gamma-\sigma^2)\big((\delta+\Gamma)s-\sigma^2\big)}{\sigma^2(1+s)^2}
--   \tag{29–30}
--   $$
--   if and only if they are given by
--   $$
--   \Phi=\mathbb 1_{\{s>s^*\}}\frac{s(1-s)\delta-2\sigma^2+\sqrt{s^2(1-s)^2\delta^2+4\sigma^4 s}}{2(1-s)},
--   \tag{31}
--   $$
--   $$
--   \Gamma=\mathbb 1_{\{s>s^*\}}\frac{-s\big((1-s)^2\delta+4\sigma^2\big)+(1+s)\sqrt{s^2(1-s)^2\delta^2+4\sigma^4 s}}{2s(1-s)} .
--   \tag{32}
--   $$
--   Moreover, as functions of $\delta$, both (31) and (32) are non-decreasing and convex on $[0,\infty)$ and strictly increasing on the shorting region $\delta>\sigma^2/s$.
--
--   This is the closed-form solution of the one-asset economy: the shorting cost and the lending yield are explicit, and they increase, at an increasing rate, with the disagreement between the optimist and the pessimist.
--
--   **Formalization Note** The system (29)–(30) is obtained in the paper from the equilibrium conditions of a continuous-time economy, which is not formalized; the proposition is stated relative to (29)–(30), which is where the paper's proof starts. The indicator $\mathbb 1_{\{s>s^*\}}$ is encoded as $\sigma^2<s\delta$. The restriction $\Gamma\ge 0$ on the left of the equivalence is a disclosed pin: on the shorting region the quadratic behind (30) also has a negative root, which solves (29)–(30) as well; the paper's proof selects "the unique strictly positive solution", and a lending yield is a non-negative flow rate. "Increasing" is read as non-decreasing on $[0,\infty)$ plus strict increase on $(\sigma^2/s,\infty)$, because both functions vanish for $\delta\le\sigma^2/s$. The endpoints $s\in\{0,1\}$, where the formulas divide by zero, are excluded.
-- source:
--   Evgeniou, Hugonnier & Prieto, Asset Pricing with Costly Short Sales, SFI Research Paper N°22-21 (version of September 22, 2022), §4.1, Proposition 3, pp. 27–28, (29)–(32); App. A, proof of Proposition 3, p. 50

import Mathlib
import Definitions.Def_CostlyShort_OneAsset_Setting

namespace CostlyShort.OneAsset

theorem proposition3_one_asset (σ s : ℝ) (hσ : 0 < σ) (hs0 : 0 < s) (hs1 : s < 1) :
    (∀ δ Φ Γ : ℝ, 0 ≤ δ → 0 ≤ Γ →
      (IsOneAssetSystem σ δ s Φ Γ ↔ Φ = costOne σ δ s ∧ Γ = yieldOne σ δ s)) ∧
    MonotoneOn (fun δ => costOne σ δ s) (Set.Ici 0) ∧
    StrictMonoOn (fun δ => costOne σ δ s) (Set.Ioi (σ ^ 2 / s)) ∧
    ConvexOn ℝ (Set.Ici 0) (fun δ => costOne σ δ s) ∧
    MonotoneOn (fun δ => yieldOne σ δ s) (Set.Ici 0) ∧
    StrictMonoOn (fun δ => yieldOne σ δ s) (Set.Ioi (σ ^ 2 / s)) ∧
    ConvexOn ℝ (Set.Ici 0) (fun δ => yieldOne σ δ s) := by sorry

end CostlyShort.OneAsset
