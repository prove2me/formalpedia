-- Prove2me | Theorems.Thm_DirectedSearch_Equilibrium_odd_dominate_even
-- name    : DirectedSearch.Equilibrium.odd_dominate_even
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:13.233126+00:00
-- url     : https://prove2.me/theorems/39db5e0a-c9a2-42d1-b258-f3335532b3c9
-- title:
--   §A.3, p. 37 — every odd iterate of the best-response map dominates every even iterate
-- statement:
--   Fix a market satisfying the standing assumptions and nonnegative assortments, and let $\tau^{(0)}\equiv0,\tau^{(1)},\tau^{(2)},\dots$ be a best-response sequence (each type's threshold in $\tau^{(k+1)}$ solves its own equation $t=\bar u_\theta(t)$ against the opposite side's thresholds in $\tau^{(k)}$). Then for every type $\theta$ and all $i,j\ge 0$,
--   $$\tau^{(2j)}_\theta\le\tau^{(2i+1)}_\theta .$$
--   Equivalently, for each type the infimum of its thresholds after odd-numbered iterations is at least the supremum of its thresholds after even-numbered iterations.
--
--   Together with the monotonicity of odd and even iterates, this lets the convergence proof of Proposition A.4 freeze one more type after every odd iteration.
--
--   **Formalization Note.** The infimum/supremum comparison of the page is stated as the equivalent pairwise inequality, so no real `sInf`/`sSup` (with their default values on unbounded sets) is involved. Inequalities are componentwise on both sides.
-- source:
--   Immorlica, Lucier, Manshadi, Wei, Designing Approximately Optimal Search on Matching Platforms, arXiv:2102.09017v2, p. 37, §A.3 proof of Proposition A.4, second claim (paragraph 3)

import Mathlib
import Definitions.Def_DirectedSearch_Equilibrium_Setting

namespace DirectedSearch.Equilibrium
theorem odd_dominate_even {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mk : Market M W) (hmk : mk.Standing) (lamM : M → W → ℝ) (lamW : W → M → ℝ)
    (hlamM : ∀ m w, 0 ≤ lamM m w) (hlamW : ∀ w m, 0 ≤ lamW w m)
    (seq : ℕ → (M → ℝ) × (W → ℝ)) (hseq : IsBRSequence mk lamM lamW seq) :
    ∀ i j : ℕ, seq (2 * j) ≤ seq (2 * i + 1) := by sorry
end DirectedSearch.Equilibrium
