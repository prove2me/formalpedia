-- Prove2me | Theorems.Thm_ExpanderBIS_HardCore_eq_8
-- name    : ExpanderBIS.HardCore.eq_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:28.525824+00:00
-- url     : https://prove2.me/theorems/fd050406-b0c1-4fca-a7ae-cd6208e252a5
-- title:
--   (8), p. 21 — for λ > (2e³Δ⁴)^{1/α}, Σ_{γ′∋v} (1 + λ)^{−α|γ′|} e^{2|γ′|} ≤ 1/Δ²
-- statement:
--   Let $\alpha > 0$, $\Delta \ge 3$, and let $G$ be a bipartite $\alpha$-expander with classes $\mathcal O, \mathcal E$ and maximum degree at most $\Delta$. Let $\lambda > (2e^3\Delta^4)^{1/\alpha}$. Then for each vertex $v$ and for the polymers of either class,
--   $$\sum_{\gamma' \ni v} (1+\lambda)^{-\alpha|\gamma'|}\, e^{2|\gamma'|} \le \frac{1}{\Delta^2},$$
--   where the sum runs over the even polymers containing $v$ (respectively the odd polymers containing $v$).
--
--   Summed over the at most $\Delta^2|\gamma|$ vertices within distance $2$ of a polymer $\gamma$, this inequality together with the weight bound gives the Kotecký–Preiss condition of §4.2.
--
--   **Formalization Note** The powers $(1+\lambda)^{-\alpha|\gamma'|}$ are real powers. The class is selected by a parameter `side` equal to $\mathcal O$ or $\mathcal E$. The standing hypotheses of §4 (bipartite $\alpha$-expander, maximum degree $\Delta$, $\Delta \ge 3$ from Theorem 1) are kept even where the inequality uses only part of them.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 21, §4.2, inequality (8), with the threshold λ > (2e³Δ⁴)^{1/α} from the same page

import Mathlib
import Definitions.Def_ExpanderBIS_HardCore_Setting

namespace ExpanderBIS.HardCore

open Finset

theorem eq_8 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (O : Finset V) (α lam : ℝ) (Δ : ℕ)
    (hα : 0 < α) (hΔ : 3 ≤ Δ)
    (hbip : IsBipartiteWrt G O) (hdeg : ∀ v, G.degree v ≤ Δ) (hG : IsBipExpander G O α)
    (hlam : (2 * Real.exp 3 * (Δ : ℝ) ^ 4) ^ (1 / α) < lam)
    (side : Finset V) (hside : side = O ∨ side = univ \ O) (v : V) :
    ∑ γ' ∈ (sidePolymers G side).filter (fun γ' => v ∈ γ'),
        (1 + lam) ^ (-(α * (#γ' : ℝ))) * Real.exp (2 * (#γ' : ℝ))
      ≤ 1 / (Δ : ℝ) ^ 2 := by sorry

end ExpanderBIS.HardCore
