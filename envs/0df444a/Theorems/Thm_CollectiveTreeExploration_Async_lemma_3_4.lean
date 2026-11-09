-- Prove2me | Theorems.Thm_CollectiveTreeExploration_Async_lemma_3_4
-- name    : CollectiveTreeExploration.Async.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:16:10.082394+00:00
-- url     : https://prove2.me/theorems/fe804e57-9d6d-4fae-8c02-c318c4a3a89f
-- title:
--   Lemma 3.4 — geometry of the fractional minimizer
-- statement:
--   Let $k\ge2$, $T$ a game tree, $y$ its fractional minimizer and $\Phi=\Phi_T(y)$. Then:
--   1. (FO) for every leaf $\ell$,
--   $$\sum_{u\in\ell\to r}d_u\,y_u^{\varepsilon}=\frac{\Phi}{k};$$
--   2. the approximate edge length $\rho_u=d_u y_u^\varepsilon$ satisfies $\frac12d_u\le\rho_u\le2d_u$ for every $u\ne r$, under (I);
--   3. the approximate height $h_u=\sum_{v\in\ell\to u}\rho_v$ does not depend on the descendant leaf $\ell\preceq u$;
--   4. $h_r=\Phi/k$.
--
--   These identities make $\rho$ an ultrametric-like length with heights $h$, used throughout the electrical analysis.
--
--   Differences from the source:
--   - encoding: finite rooted weighted trees and leaf configurations of total mass k → finite sets of natural-number labels, a parent map, positive non-root lengths and zero-extended leaf masses, with descendant paths including the lower endpoint only; reason: every source tree admits these labels, with no size, length or mass restriction; tree validity uses the published general tree type without its separate HST restrictions
--   - encoding: under (I) → an integral configuration x of total mass k, with the three explicit leaf inequalities (I); reason: (I) is a property of the pair (x, y)
-- source:
--   Romain Cosson, Laurent Massoulié, Polylogarithmic Collective Tree Exploration, STOC 2027 submission #263 (October 2026), source.pdf sha256 54f5e43ddf9269e11a2fff4aa4b0ea62348afe16a38aba551313f43cbf3e00e0; Lemma 3.4, p.8; proof pp.8–9

import Mathlib
import Definitions.Def_CollectiveTreeExploration_Async_PowerRegularizer

namespace CollectiveTreeExploration.Async

open scoped BigOperators ENNReal

/-- **Lemma 3.4** (geometry of the fractional minimizer, p.8). (FO): for every leaf `ℓ`,
`∑_{u ∈ ℓ → r} d_u y_u^ε = Φ/k`. Under (I), `d_u/2 ≤ ρ_u ≤ 2 d_u` for every `u ≠ r`. The
approximate height `h_u = ∑_{v ∈ ℓ → u} ρ_v` does not depend on the descendant leaf `ℓ ⪯ u`, and
`h_r = Φ/k`. -/
theorem lemma_3_4 (k : ℕ) (hk : 2 ≤ k) (T : WTree) (hT : T.IsGameTree) :
    (∀ ℓ ∈ T.leaves, ∑ u ∈ T.pathVerts ℓ T.root, T.len u * (T.mass (T.fracMin k) u) ^ eps k =
      T.Phi k (T.fracMin k) / k) ∧
    (∀ x : ℕ → ℕ, T.IsIntConfig k x → T.InvI x (T.fracMin k) →
      ∀ u ∈ T.V, u ≠ T.root → T.len u / 2 ≤ T.rho k u ∧ T.rho k u ≤ 2 * T.len u) ∧
    (∀ u ∈ T.V, ∀ ℓ ∈ T.leavesBelow u, ∀ ℓ' ∈ T.leavesBelow u,
      T.approxHeightVia k u ℓ = T.approxHeightVia k u ℓ') ∧
    T.hgt k T.root = T.Phi k (T.fracMin k) / k := by sorry

end CollectiveTreeExploration.Async
