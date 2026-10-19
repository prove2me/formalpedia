-- Prove2me | Theorems.Thm_BundledExpansion_SeqSim_root_equation_8
-- name    : BundledExpansion.SeqSim.root_equation_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:05.758422+00:00
-- url     : https://prove2.me/theorems/7eeea644-232e-4b0b-856b-aef5f5ed5442
-- title:
--   Equation (8), p. 15 — unique sequential split time
-- statement:
--   For any subinterval $[s,e]\subseteq[0,T]$ and either choice $l$ of leading cluster, let $f$ be the other type. The balance equation for the final expansion has exactly one solution $y$ strictly between $s$ and $e$:
--
--   $$
--   \frac{a_{ll}}{a_{fl}}D_f(s,y)+\frac{a_{lf}}{a_{ff}}D_f(y,e)=D_l(s,e),\qquad s<y<e.
--   $$
--
--   This pins down the final split time independently of how many earlier leading expansions are used. **Formalization Note** The paper states uniqueness without a regularity premise; this statement assumes continuous demand and the strict demand-ratio guard, which make the equation strictly monotone. Lean’s indices are 0 and 1 for the paper’s 1 and 2.
-- source:
--   Arbabian, Chen & Moinzadeh, Capacity Expansions with Bundled Supplies of Attributes, SSRN 3085349 (manuscript of April 14, 2019), https://ssrn.com/abstract=3085349, p. 15 (PDF 16), §4.1, equation (8)

import Mathlib
import Definitions.Def_BundledExpansion_SeqSim_Model

namespace BundledExpansion.SeqSim

theorem root_equation_8 (P : Params) (hS : P.Standing) (hR : P.Regular)
    (hG : P.RatioGuard) (l : Fin 2) (s e : ℝ)
    (hs : 0 ≤ s) (he : e ≤ P.T) (hse : s < e) :
    ∃! y : ℝ, y ∈ Set.Ioo s e ∧
      P.a l l / P.a (other l) l * D P (other l) s y +
        P.a l (other l) / P.a (other l) (other l) * D P (other l) y e =
          D P l s e := by sorry

end BundledExpansion.SeqSim
