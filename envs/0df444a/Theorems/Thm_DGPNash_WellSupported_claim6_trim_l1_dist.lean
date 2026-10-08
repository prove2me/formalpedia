-- Prove2me | Theorems.Thm_DGPNash_WellSupported_claim6_trim_l1_dist
-- name    : DGPNash.WellSupported.claim6_trim_l1_dist
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:49:59.500438+00:00
-- url     : https://prove2.me/theorems/5e01c10d-fa71-4e47-b160-9a8eb9f5c1b6
-- title:
--   Claim 6 — the trimmed profile is within L1 distance 2/(k−1) of x
-- statement:
--   Let $x$ be an $\epsilon$-approximate Nash equilibrium of a game in normal form with $r\ge 2$ players and nonnegative payoffs, let $k>1$, and let $\hat x$ be the trimmed profile:
--   $$\hat x^p_j=\begin{cases}\dfrac{x^p_j}{1-z^p}, & \mathcal U^p_j\ge\mathcal U^p_{\max}-\epsilon k,\\[4pt] 0, & \text{otherwise,}\end{cases}$$
--   with $z^p$ the mass that $x^p$ puts on strategies $j$ with $\mathcal U^p_j<\mathcal U^p_{\max}-\epsilon k$. Then for every player $p$,
--   $$\sum_{j\in S_p}\bigl|x^p_j-\hat x^p_j\bigr|\ \le\ \frac{2}{k-1}.$$
--
--   Combined with the Lipschitz bound of Lemma 4.26, this shows that trimming changes every expected payoff $\mathcal U^p_j$ by little.
--
--   **Formalization Note.** $r\ge2$ and $u\ge0$ are the standing assumptions of Sec. 2.1. The condition $k>1$ is what makes $1-z^p>0$ through Claim 5; the paper's $k$ in the final step is $1+1/\sqrt\epsilon>1$.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), p. 244, Sec. 4.7, Claim 6

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_WellSupported_Equilibria

namespace DGPNash.WellSupported

open Finset

/-- **Claim 6** (Daskalakis–Goldberg–Papadimitriou 2009, p. 244): if `x` is an
`ε`-approximate Nash equilibrium of a game with nonnegative payoffs and at least two players, and
`k > 1`, then for every player `p` the trimmed profile `x̂ = trim u x ε k` satisfies
`Σ_{j ∈ S_p} |x^p_j − x̂^p_j| ≤ 2/(k − 1)`. -/
theorem claim6_trim_l1_dist {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (hu : ∀ p s, 0 ≤ u p s) (hr : 2 ≤ Fintype.card ι)
    (x : ∀ i, S i → ℝ) (ε : ℝ) (hx : IsEpsApproxNash u x ε) (k : ℝ) (hk : 1 < k) (p : ι) :
    ∑ j : S p, |x p j - trim u x ε k p j| ≤ 2 / (k - 1) := by sorry

end DGPNash.WellSupported
