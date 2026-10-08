-- Prove2me | Theorems.Thm_DGPNash_WellSupported_claim5_trimMass_le
-- name    : DGPNash.WellSupported.claim5_trimMass_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:49:49.809485+00:00
-- url     : https://prove2.me/theorems/8ea81041-84e6-4fdb-8d09-2fa6d6113e3d
-- title:
--   Claim 5 — the mass on εk-suboptimal strategies is at most 1/k
-- statement:
--   Let $x$ be an $\epsilon$-approximate Nash equilibrium of a game in normal form with $r\ge 2$ players and nonnegative payoffs, and let $k>0$. For each player $p$ let
--   $$z^p=\sum_{j\in S_p}x^p_j\cdot\mathcal X_{\{\mathcal U^p_j<\mathcal U^p_{\max}-\epsilon k\}},$$
--   the probability that $x^p$ assigns to pure strategies whose expected payoff $\mathcal U^p_j$ is more than $\epsilon k$ below $\mathcal U^p_{\max}$. Then for all $p$,
--   $$z^p\le\frac1k .$$
--
--   The claim controls how much probability is removed when these strategies are deleted, and so how far the trimmed profile is from $x$ (Claim 6).
--
--   **Formalization Note.** $r\ge2$ and $u\ge0$ are the standing assumptions of Sec. 2.1. The paper leaves $k$ "to be specified later"; the claim is stated for every $k>0$.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), pp. 243–244, Sec. 4.7, Claim 5

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_WellSupported_Equilibria

namespace DGPNash.WellSupported

open Finset

/-- **Claim 5** (Daskalakis–Goldberg–Papadimitriou 2009, pp. 243–244): if `x` is an
`ε`-approximate Nash equilibrium of a game with nonnegative payoffs and at least two players, then
for every `k > 0` and every player `p`, the mass
`z^p = Σ_j x^p_j · 𝒳_{\{𝒰^p_j < 𝒰^p_max − εk\}}` satisfies `z^p ≤ 1/k`. -/
theorem claim5_trimMass_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (hu : ∀ p s, 0 ≤ u p s) (hr : 2 ≤ Fintype.card ι)
    (x : ∀ i, S i → ℝ) (ε : ℝ) (hx : IsEpsApproxNash u x ε) (k : ℝ) (hk : 0 < k) (p : ι) :
    trimMass u x ε k p ≤ 1 / k := by sorry

end DGPNash.WellSupported
