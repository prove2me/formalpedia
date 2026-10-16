-- Prove2me | Theorems.Thm_DirectedSearch_Equilibrium_odd_even_monotone
-- name    : DirectedSearch.Equilibrium.odd_even_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:12.049449+00:00
-- url     : https://prove2.me/theorems/443df8ad-953a-4509-9bda-cc294e95debd
-- title:
--   §A.3, p. 37 — odd iterates of the best-response map decrease, even iterates increase
-- statement:
--   Fix a market satisfying the standing assumptions and nonnegative assortments $\lambda_m(w)$, $\lambda_w(m)$. Let $\tau^{(0)},\tau^{(1)},\dots$ be a best-response sequence: $\tau^{(0)}\equiv 0$, and for each $k$ every type's threshold in $\tau^{(k+1)}$ solves its own equation $t=\bar u_\theta(t)$ against the opposite side's thresholds in $\tau^{(k)}$. Then, for every type $\theta$ and every $k\ge0$,
--   $$\tau^{(2k+3)}_\theta\le\tau^{(2k+1)}_\theta\qquad\text{and}\qquad\tau^{(2k)}_\theta\le\tau^{(2k+2)}_\theta .$$
--   That is, the thresholds after an odd number of iterations form a weakly decreasing sequence, and those after an even number of iterations a weakly increasing one.
--
--   This is the first step of the convergence proof of the best-response iteration (Proposition A.4).
--
--   **Formalization Note.** The inequalities are componentwise on both sides. The best-response step is the one of Appendix A.3: each type's new threshold is its best-response expected utility, i.e. the solution of its own fixed-point equation (Lemma A.3), not formula (5) evaluated at the old profile.
-- source:
--   Immorlica, Lucier, Manshadi, Wei, Designing Approximately Optimal Search on Matching Platforms, arXiv:2102.09017v2, p. 37, §A.3 proof of Proposition A.4, first claim (paragraph 2)

import Mathlib
import Definitions.Def_DirectedSearch_Equilibrium_Setting

namespace DirectedSearch.Equilibrium
theorem odd_even_monotone {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mk : Market M W) (hmk : mk.Standing) (lamM : M → W → ℝ) (lamW : W → M → ℝ)
    (hlamM : ∀ m w, 0 ≤ lamM m w) (hlamW : ∀ w m, 0 ≤ lamW w m)
    (seq : ℕ → (M → ℝ) × (W → ℝ)) (hseq : IsBRSequence mk lamM lamW seq) :
    (∀ k : ℕ, seq (2 * k + 3) ≤ seq (2 * k + 1)) ∧ (∀ k : ℕ, seq (2 * k) ≤ seq (2 * k + 2)) := by sorry
end DirectedSearch.Equilibrium
