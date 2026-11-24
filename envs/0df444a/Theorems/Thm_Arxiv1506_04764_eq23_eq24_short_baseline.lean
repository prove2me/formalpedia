-- Prove2me | Theorems.Thm_Arxiv1506_04764_eq23_eq24_short_baseline
-- name    : Arxiv1506_04764.eq23_eq24_short_baseline
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T14:53:14.067901+00:00
-- url     : https://prove2.me/theorems/8ee3c4af-5099-4625-a08d-488cbd6584a4
-- title:
--   Eqs. (23)-(24): expansion in the baseline (as proved)
-- statement:
--   Write $\Delta r=r_2'-r_1'$ and $\varepsilon=|\Delta r|/|r_1'-r''|$.
--
--   (23) There are $C$ and $\delta>0$ such that for all $r_1',r_2'$ and $r''\neq r_1'$ with $\varepsilon\le\delta$,
--   $$\Big|\,|r_2'-r''|-\big(|r_1'-r''|+\Delta r\cdot\hat e_{r_1'-r''}\big)\Big|\le C\,\varepsilon^2|r_1'-r''|.$$
--
--   (24) There are $C$ and $\delta>0$ such that for all $r_1',r_2'$, $r''\neq r_1'$ and $\beta$ with $\varepsilon\le\delta$,
--   $$\big|\hat e_{r_2'-r''}\cdot\beta-\hat e_{r_1'-r''}\cdot\beta\big|\le C\,|\beta|\,\varepsilon.$$
--
--   **Formalization Note** The paper states both approximations "to first order in $|\Delta r|/|r_1'-r''|$". For (23) this is the bound above. For (24) the error is of first order, not second: with $r_1'-r''=(0,0,1)$, $\Delta r=(\varepsilon,0,0)$ and $\beta$ along $x$, the difference equals $|\beta|\varepsilon/\sqrt{1+\varepsilon^2}$. So (24) holds with an $O(\varepsilon)$ error, which is what is stated (as proved).
-- source:
--   Braun, Monjid, Rougé and Kerr, Generalization of the Van Cittert-Zernike theorem: observers moving with respect to sources, arXiv:1506.04764v1 (2015), claim c008; Sec. 2.4, eqs. (23)-(24), PDF p. 8

import Mathlib
import Definitions.Def_Arxiv1506_04764_Basic

open MeasureTheory Complex

namespace Arxiv1506_04764

theorem eq23_eq24_short_baseline :
    (∃ C δ : ℝ, 0 < δ ∧ ∀ r1 r2 r'' : V3, r1 ≠ r'' → len (r2 - r1) ≤ δ * len (r1 - r'') →
      |len (r2 - r'') - (len (r1 - r'') + dotProduct (r2 - r1) (unitVec (r1 - r'')))| ≤
        C * len (r2 - r1) ^ 2 / len (r1 - r'')) ∧
    (∃ C δ : ℝ, 0 < δ ∧ ∀ r1 r2 r'' beta : V3, r1 ≠ r'' → len (r2 - r1) ≤ δ * len (r1 - r'') →
      |dotProduct (unitVec (r2 - r'')) beta - dotProduct (unitVec (r1 - r'')) beta| ≤
        C * len beta * (len (r2 - r1) / len (r1 - r''))) := by sorry

end Arxiv1506_04764
