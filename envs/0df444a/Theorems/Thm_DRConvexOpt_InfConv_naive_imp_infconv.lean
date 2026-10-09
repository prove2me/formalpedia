-- Prove2me | Theorems.Thm_DRConvexOpt_InfConv_naive_imp_infconv
-- name    : DRConvexOpt.InfConv.naive_imp_infconv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:45.697065+00:00
-- url     : https://prove2.me/theorems/0b3acb4a-1133-46fc-9b32-d6570f22227f
-- title:
--   Proof of Theorem 3, p. 37 — the naïve approximation (6) implies the infimal convolution bound (7)
-- statement:
--   Let $\mathcal P$ be the standardized ambiguity set satisfying (C2), $\{\mathcal I_j\}_{j\in\mathcal J}$ a partition with outer approximations $\mathcal P^j$, and $v$ as in (C3). Assume the uniform first-moment bound: for each $j$ there is $M_j$ with $\mathbb E_{\mathbb P}\|\tilde z\| \le M_j$ for all $\mathbb P \in \mathcal P^j$. Then for every $x \in \mathbb R^N$ and $w \in \mathbb R$,
--   $$\min_{j\in\mathcal J}\sup_{\mathbb P\in\mathcal P^j}\mathbb E_{\mathbb P}[v(x,\tilde z)] \le w \quad\Longrightarrow\quad \inf_{(y,\delta)\in\Gamma(x)}\sum_{j\in\mathcal J}\delta_j\sup_{\mathbb P\in\mathcal P^j}\mathbb E_{\mathbb P}[v(y_j/\delta_j,\tilde z)] \le w.$$
--
--   This is the first implication in the chain of Theorem 3: the infimal convolution bound is at least as tight as the naïve approximation.
--
--   **Formalization Note** The uniform first-moment bound is an **added, disclosed hypothesis**; without it the implication is false. Example: $P = 1$, $Q = K = 0$, $\mathcal C_1 = [0,\tfrac12]$ with probability in $[\tfrac12, 1]$, $\mathcal C_2 = [0,1]$ with probability $1$, the singleton partition, $v(x,z) = z$ and $w = 1$: then (6) holds through $\mathcal P^2$, but $\tfrac12\delta_0 + \tfrac12\delta_M \in \mathcal P^1$ for every $M$, so the $\mathcal P^1$ term is $+\infty$ for every $\delta_1 > 0$ and (7) fails. Both bounds are `EReal`-valued.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 37, proof of Theorem 3, second paragraph

import Mathlib
import Definitions.Def_DRConvexOpt_InfConv_Setting

namespace DRConvexOpt.InfConv

open MeasureTheory Matrix Filter Topology

/-- Proof of Theorem 3, p. 37: the naïve approximation (6) implies the infimal convolution bound (7),
under the disclosed assumption `UnifFirstMoment` (without it the implication is false). -/
theorem naive_imp_infconv {nP nQ nK nI nN nL nJ : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (v : PWAff nN nP nL) (blk : Fin (nI + 1) → Fin nJ)
    (hC2 : ∃ μ ∈ ambiguitySet d, ∀ i, d.plo i < d.phi i →
      μ.real (d.conf i) ∈ Set.Ioo (d.plo i) (d.phi i))
    (hFM : UnifFirstMoment d blk) (x : Fin nN → ℝ) (w : ℝ) :
    naiveBound d blk v x ≤ (w : EReal) → infConvBound d blk v x ≤ (w : EReal) := by sorry

end DRConvexOpt.InfConv
