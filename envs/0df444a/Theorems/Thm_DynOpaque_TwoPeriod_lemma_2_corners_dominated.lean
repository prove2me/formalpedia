-- Prove2me | Theorems.Thm_DynOpaque_TwoPeriod_lemma_2_corners_dominated
-- name    : DynOpaque.TwoPeriod.lemma_2_corners_dominated
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:31.000029+00:00
-- url     : https://prove2.me/theorems/dc4df5a4-f39f-4e33-8cfb-d52f264a6325
-- title:
--   Proof of Proposition 1, pp. 30–31 — outside the interior regimes of Lemma 2, p1 = p2 = vHL is dominated by transparent selling
-- statement:
--   Assume $v_H>v_L$, $c_H>c_L$, $0\le\alpha\le1$, $c_L\le v_L$, let $v_{HL}=\frac{v_H-v_L}{2}+v_L$ and $r=\frac{v_{HL}-c_L}{c_H-c_L}$, and suppose that one of the following holds:
--
--   1. $\alpha<\frac{\sqrt{17}-3}{2}$ and $\frac{4-4\alpha-\alpha^2}{2-\alpha-\alpha^2}\le r$;
--   2. $\frac{\sqrt{17}-3}{2}\le\alpha\le1$ and $\frac{2}{1+\alpha}\le r$.
--
--   Then for every $(\xi_1,\xi_2)\in[0,1]^2$, objective (3) satisfies
--   $$
--   \Pi(\xi_1,\xi_2\mid v_{HL},v_{HL})\ \le\ 2\max\{v_H-c_H,\ v_L-c_L\}.
--   $$
--
--   So the policy $p_1=p_2=v_{HL}$ can be optimal only in the interior regimes of Lemma 2; in the corner regimes ($\xi_1=1$) the best transparent policy does at least as well. This is the second step of the paper's proof of Proposition 1.
--
--   **Formalization Note** The statement covers $\alpha=1$, where the proof on p. 31 also runs; Lemma 2 (ii) itself is printed for $\alpha<1$.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927, pp. 30–31, proof of Proposition 1, second to fourth paragraphs

import Mathlib
import Definitions.Def_DynOpaque_TwoPeriod_Model

namespace DynOpaque.TwoPeriod

/-- Proof of Proposition 1, pp. 30–31: outside the interior regimes of Lemma 2, objective (3)
never exceeds the best transparent profit `2 max{vH − cH, vL − cL}`. -/
theorem lemma_2_corners_dominated (vH vL cH cL α : ℝ) (hS : Standing vH vL cH cL α)
    (hreg : (α < alphaBar ∧
        (4 - 4 * α - α ^ 2) / (2 - α - α ^ 2) ≤ (vHL vH vL - cL) / (cH - cL)) ∨
      (alphaBar ≤ α ∧ α ≤ 1 ∧ 2 / (1 + α) ≤ (vHL vH vL - cL) / (cH - cL))) :
    ∀ x ∈ box, obj3 vH vL cH cL α x.1 x.2 ≤ 2 * max (vH - cH) (vL - cL) := by sorry

end DynOpaque.TwoPeriod
