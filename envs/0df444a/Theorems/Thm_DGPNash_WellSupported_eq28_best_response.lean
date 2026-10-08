-- Prove2me | Theorems.Thm_DGPNash_WellSupported_eq28_best_response
-- name    : DGPNash.WellSupported.eq28_best_response
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:49:46.740219+00:00
-- url     : https://prove2.me/theorems/a474b116-22d2-46fd-aa54-b1987e66b07d
-- title:
--   Sec. 4.7, Eq. (28) — an ε-approximate Nash equilibrium is ε-close to a best response
-- statement:
--   Let $x$ be an $\epsilon$-approximate Nash equilibrium of a game in normal form with $r\ge 2$ players and nonnegative payoffs $u^p_s\ge 0$. With $\mathcal U^p_j=\sum_{s\in S_{-p}}u^p_{js}x_s$ the expected payoff of player $p$ for the pure strategy $j$, and $\mathcal U^p_{\max}=\max_j\mathcal U^p_j$, every player $p$ satisfies
--   $$\sum_{j\in S_p}\mathcal U^p_j\,x^p_j\ \ge\ \mathcal U^p_{\max}-\epsilon .$$
--
--   This is the approximate-equilibrium inequality tested against a pure best response, and is the form in which the hypothesis enters the bound on the trimmed mass (Claim 5).
--
--   **Formalization Note.** $r\ge2$ and $u\ge0$ are the standing assumptions of Sec. 2.1 (p. 199) and are stated as hypotheses although this step does not use them. $\epsilon$ is not constrained: an $\epsilon$-approximate equilibrium can exist only for $\epsilon\ge 0$.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), p. 243, Sec. 4.7, Eq. (28)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_WellSupported_Equilibria

namespace DGPNash.WellSupported

open Finset

/-- **Sec. 4.7, Eq. (28)** (Daskalakis–Goldberg–Papadimitriou 2009, p. 243): if `x` is an
`ε`-approximate Nash equilibrium of a game with nonnegative payoffs and at least two players, then
for every player `p`, `Σ_j 𝒰^p_j x^p_j ≥ 𝒰^p_max − ε`. -/
theorem eq28_best_response {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (hu : ∀ p s, 0 ≤ u p s) (hr : 2 ≤ Fintype.card ι)
    (x : ∀ i, S i → ℝ) (ε : ℝ) (hx : IsEpsApproxNash u x ε) (p : ι) :
    ∑ j : S p, DGPNash.NashMap.purePayoff u x p j * x p j ≥ maxPurePayoff u x p - ε := by sorry

end DGPNash.WellSupported
