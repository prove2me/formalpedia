-- Prove2me | Theorems.Thm_DataTrackComp_Surplus_lemma_1
-- name    : DataTrackComp.Surplus.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:39.034528+00:00
-- url     : https://prove2.me/theorems/438309b4-c13b-44ad-9d93-35c407ca11cc
-- title:
--   Lemma 1, pp. OA-2–OA-3 — continuation equilibrium after product-1 prices in the forward-looking setting
-- statement:
--   Consider the forward-looking setting with $\bar u>0$ and $m>0$, and product-1 prices $p^A_1\in[0,1]$, $p^B_1\in[-1/2,1]$. Take any equilibrium of the continuation game after these prices: the consumer's mixed period-1 choice $\gamma_1$, firm B's tracked product-2 prices $p^T(\tau)$, and its untracked price $p^U$. Then the following hold.
--
--   1. For every type $(s,\theta)$ of the square with $\theta>0$, the tracked price equals the consumer's valuation: $p^T(s,\theta)=m\theta$.
--   2. If $p^B_1-p^A_1\le-1/2$, the consumer buys product 1 from firm B with probability one, for $\mu_0$-almost every type.
--   3. If $p^B_1-p^A_1>-1/2$, firm B's untracked price is
--   $$p^U=m\,\bar\theta\!\left(\bar X(p^A_1,p^B_1),m\right),$$
--   and for every type $(s,\theta)$ of the square: if $s>g(\theta\mid p^A_1,p^B_1)$ she buys from B with probability one, and if $s<g(\theta\mid p^A_1,p^B_1)$ she buys from A with probability one.
--
--   Here $\bar X$, $\bar\theta$ and $g$ are (B.1), (B.2) and (B.4).
--
--   This lemma characterizes play after every pair of product-1 prices. It is what reduces the dynamic game to the static game $\mathbf G(m)$.
--
--   **Formalization Note.** Two conventions differ from the page. The tracked price is pinned only for $\theta>0$, since at $\theta=0$ every nonnegative price is optimal. The consumer buys product 2 if and only if its price is at most $m\theta$, so "buys if $\theta>\bar\theta$" holds up to the null tie $\theta=\bar\theta$.
-- source:
--   Bimpikis, Morgenstern & Saban, Data Tracking under Competition, authors' manuscript with online appendix (Operations Research, doi:10.1287/opre.2023.2489; PDF of 2023-05-04), pp. OA-2–OA-3 (PDF 37–38), Lemma 1

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_Game
import Definitions.Def_DataTrackComp_Surplus_ReducedGame
open MeasureTheory

namespace DataTrackComp.Surplus

theorem lemma_1 (ubar m pA pB : ℝ) (hu : 0 < ubar) (hm : 0 < m) (hpA : pA ∈ SA)
    (hpB : pB ∈ SB) (c : Cont) (hc : IsContEq .forward ubar m pA pB c) :
    (∀ τ ∈ square, 0 < τ.2 → c.pT τ = m * τ.2) ∧
    (pB - pA ≤ -1 / 2 → ∀ᵐ τ ∂μ0, c.γ1 τ = 1) ∧
    (-1 / 2 < pB - pA →
      c.pU = m * thetaBar (Xbar pA pB) m ∧
      ∀ τ ∈ square, (gfun m pA pB τ.2 < τ.1 → c.γ1 τ = 1) ∧
        (τ.1 < gfun m pA pB τ.2 → c.γ1 τ = 0)) := by sorry

end DataTrackComp.Surplus
