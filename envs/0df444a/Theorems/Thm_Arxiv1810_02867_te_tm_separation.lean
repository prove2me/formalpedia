-- Prove2me | Theorems.Thm_Arxiv1810_02867_te_tm_separation
-- name    : Arxiv1810_02867.te_tm_separation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T05:16:17.089035+00:00
-- url     : https://prove2.me/theorems/53450667-cfa3-5c6e-ae99-cd62d73f68ae
-- title:
--   Eqs. (A17)-(A22): separation into TE and TM waves
-- statement:
--   Let the fields $E,H$, the sources $J^{\rm e},J^{\rm m}$ and the parameters $\varepsilon^o,\xi,\mu$ be independent of $x_2$ and satisfy (A15)-(A16). Assume $\varepsilon^o$ and $\mu$ are symmetric. Assume further
--   $$\varepsilon^o_{21}=\varepsilon^o_{23}=0,\quad \mu_{21}=\mu_{23}=0,\quad \xi_{11}=\xi_{22}=\xi_{33}=\xi_{13}=\xi_{31}=0.$$
--   Then, in the $(x_1,x_3)$-plane, $(E_2,H_1,H_3)$ satisfy the transverse-electric system (A17)-(A19):
--   $$\varepsilon^o_{22}\partial_tE_2+\xi_{21}\partial_tH_1+\xi_{23}\partial_tH_3+\partial_1H_3-\partial_3H_1=-J^{\rm e}_2,$$
--   $$\mu_{11}\partial_tH_1+\mu_{31}\partial_tH_3+\xi_{21}\partial_tE_2-\partial_3E_2=-J^{\rm m}_1,\qquad \mu_{31}\partial_tH_1+\mu_{33}\partial_tH_3+\xi_{23}\partial_tE_2+\partial_1E_2=-J^{\rm m}_3.$$
--   In addition, $(H_2,E_1,E_3)$ satisfy the transverse-magnetic system (A20)-(A22):
--   $$\mu_{22}\partial_tH_2+\xi_{12}\partial_tE_1+\xi_{32}\partial_tE_3-\partial_1E_3+\partial_3E_1=-J^{\rm m}_2,$$
--   $$\varepsilon^o_{11}\partial_tE_1+\varepsilon^o_{31}\partial_tE_3+\xi_{12}\partial_tH_2+\partial_3H_2=-J^{\rm e}_1,\qquad \varepsilon^o_{31}\partial_tE_1+\varepsilon^o_{33}\partial_tE_3+\xi_{32}\partial_tH_2-\partial_1H_2=-J^{\rm e}_3.$$
--
--   **Formalization Note** The $x_2$-independent quantities are restricted to the plane $x_2=0$. The symmetry of $\varepsilon^o$ and $\mu$, which the paper invokes as $\varepsilon^o_{13}=\varepsilon^o_{31}$ and $\mu_{13}=\mu_{31}$, is assumed in full: the reduction also uses $\varepsilon^o_{12}=\varepsilon^o_{21}$, $\varepsilon^o_{32}=\varepsilon^o_{23}$, $\mu_{12}=\mu_{21}$ and $\mu_{32}=\mu_{23}$.
-- source:
--   Wapenaar and Reinicke, Unified wave field retrieval and imaging method for inhomogeneous non-reciprocal media, arXiv:1810.02867v2 (2020), claim c023; Appendix A.1, eqs. (A15)-(A22), PDF pp. 22-23

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

open MeasureTheory Matrix

namespace Arxiv1810_02867

theorem te_tm_separation (eO xi mu : Space → Fin 3 → Fin 3 → ℝ)
    (E H Je Jm : Space → ℝ → Fin 3 → ℝ)
    (hiE : IndepX2 E) (hiH : IndepX2 H) (hiJe : IndepX2 Je) (hiJm : IndepX2 Jm)
    (hieO : IndepX2 eO) (hixi : IndepX2 xi) (himu : IndepX2 mu)
    (heOsym : ∀ x i l, eO x i l = eO x l i) (hmusym : ∀ x j k, mu x j k = mu x k j)
    (heO0 : ∀ x, eO x 1 0 = 0 ∧ eO x 1 2 = 0) (hmu0 : ∀ x, mu x 1 0 = 0 ∧ mu x 1 2 = 0)
    (hxi0 : ∀ x, xi x 0 0 = 0 ∧ xi x 1 1 = 0 ∧ xi x 2 2 = 0 ∧ xi x 0 2 = 0 ∧ xi x 2 0 = 0)
    (hM : MaxwellEO eO xi mu E H Je Jm) :
    TESystem (restr eO) (restr xi) (restr mu) (restr E) (restr H) (restr Je) (restr Jm) ∧
    TMSystem (restr eO) (restr xi) (restr mu) (restr E) (restr H) (restr Je) (restr Jm) := by sorry

end Arxiv1810_02867
