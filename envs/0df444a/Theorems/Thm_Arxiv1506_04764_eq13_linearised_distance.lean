-- Prove2me | Theorems.Thm_Arxiv1506_04764_eq13_linearised_distance
-- name    : Arxiv1506_04764.eq13_linearised_distance
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T14:22:13.882614+00:00
-- url     : https://prove2.me/theorems/d81696e6-36e3-4504-8bc1-e1dac5c96795
-- title:
--   Eq. (13): linearisation of the antenna-source distance
-- statement:
--   There are constants $C$ and $\delta>0$ such that for all antenna positions $r'$, source points $r''\neq r'$, velocities $v_s$ and times $t'$ with $|v_st'|\le\delta|r'-r''|$,
--
--   $$\Big|\,|r'+v_st'-r''|-\big(|r'-r''|+\hat e_{r'-r''}\cdot v_st'\big)\Big|\le C\,\frac{|v_st'|^2}{|r'-r''|}.$$
--
--   That is, $R(t')=|r'+v_st'-r''|\simeq|r'-r''|+\hat e_{r'-r''}\cdot v_st'$ to first order in $v_st'/|r'-r''|$, with an error of relative order $(v_st'/|r'-r''|)^2$.
--
--   **Formalization Note** The paper's "$\simeq$ to first order in $v_st'/|r'-r''|\ll1$" is stated as an explicit remainder bound, uniform in all quantities, valid when the ratio is at most some fixed $\delta>0$. The numerical claims of the paragraph (pixel size, $t'\lesssim1$ s or $100$ s) are not part of the statement.
-- source:
--   Braun, Monjid, Rougé and Kerr, Generalization of the Van Cittert-Zernike theorem: observers moving with respect to sources, arXiv:1506.04764v1 (2015), claim c004; Sec. 2.2, eq. (13) and the paragraph before it, PDF pp. 5-6

import Mathlib
import Definitions.Def_Arxiv1506_04764_Basic

open MeasureTheory Complex

namespace Arxiv1506_04764

theorem eq13_linearised_distance :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ (r' r'' vs : V3) (t' : ℝ), r' ≠ r'' →
      len (t' • vs) ≤ δ * len (r' - r'') →
      |len (r' + t' • vs - r'') -
          (len (r' - r'') + dotProduct (unitVec (r' - r'')) (t' • vs))| ≤
        C * len (t' • vs) ^ 2 / len (r' - r'') := by sorry

end Arxiv1506_04764
