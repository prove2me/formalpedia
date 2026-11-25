-- Prove2me | Theorems.Thm_Arxiv1810_02867_unified_form_table1
-- name    : Arxiv1810_02867.unified_form_table1
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T05:20:05.59119+00:00
-- url     : https://prove2.me/theorems/baac9634-1378-4aee-bc57-7021c73d8adf
-- title:
--   Eqs. (A71)-(A72) with Table 1: TE, TM, SH and AC waves in unified form
-- statement:
--   Each of the four systems in the $(x_1,x_3)$-plane holds if and only if the unified equations (A71)-(A72)
--   $$\alpha\partial_tP+(\partial_r+\gamma_r\partial_t)Q_r=B,\qquad (\partial_s+\gamma_s\partial_t)P+\beta_{su}\partial_tQ_u=C_s$$
--   hold with the quantities of Table 1, where $\beta_{13}=\beta_{31}$:
--
--   1. TE (A17)-(A19): $P=E_2$, $Q_1=H_3$, $Q_3=-H_1$, $\alpha=\varepsilon^o_{22}$, $\beta_{11}=\mu_{33}$, $\beta_{31}=-\mu_{31}$, $\beta_{33}=\mu_{11}$, $\gamma_1=\xi_{23}$, $\gamma_3=-\xi_{21}$, $B=-J^{\rm e}_2$, $C_1=-J^{\rm m}_3$, $C_3=J^{\rm m}_1$;
--   2. TM (A20)-(A22): $P=H_2$, $Q_1=-E_3$, $Q_3=E_1$, $\alpha=\mu_{22}$, $\beta_{11}=\varepsilon^o_{33}$, $\beta_{31}=-\varepsilon^o_{31}$, $\beta_{33}=\varepsilon^o_{11}$, $\gamma_1=-\xi_{32}$, $\gamma_3=\xi_{12}$, $B=-J^{\rm m}_2$, $C_1=J^{\rm e}_3$, $C_3=-J^{\rm e}_1$;
--   3. SH (A45)-(A47): $P=v_2$, $Q_1=-\tau_{21}$, $Q_3=-\tau_{23}$, $\alpha=\rho^o_{22}$, $\beta_{11}=4s_{1221}$, $\beta_{31}=4s_{1223}$, $\beta_{33}=4s_{3223}$, $\gamma_1=2\xi_{221}$, $\gamma_3=2\xi_{223}$, $B=F_2$, $C_1=2h_{21}$, $C_3=2h_{23}$;
--   4. AC (A68)-(A70): $P=p$, $Q_1=v_1$, $Q_3=v_3$, $\alpha=\kappa$, $\beta_{11}=\rho^o_{11}$, $\beta_{31}=\rho^o_{31}$, $\beta_{33}=\rho^o_{33}$, $\gamma_1=\xi_1$, $\gamma_3=\xi_3$, $B=q$, $C_1=F_1$, $C_3=F_3$.
--
--   **Formalization Note** The paper says the four systems "can all be cast in" the unified form. Each unified equation is one of the system's equations up to sign, so the statement is an equivalence.
-- source:
--   Wapenaar and Reinicke, Unified wave field retrieval and imaging method for inhomogeneous non-reciprocal media, arXiv:1810.02867v2 (2020), claim c028; Appendix A.4, eqs. (A71)-(A72), with Table 1 (Section II, PDF p. 4), PDF p. 28

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

open MeasureTheory Matrix

namespace Arxiv1810_02867

theorem unified_form_table1 :
    (∀ (eO xi mu : Plane → Fin 3 → Fin 3 → ℝ) (E H Je Jm : Plane → ℝ → Fin 3 → ℝ),
      TESystem eO xi mu E H Je Jm ↔
        UnifiedEqs (fun x => eO x 1 1)
          (fun x => ![![mu x 2 2, -mu x 2 0], ![-mu x 2 0, mu x 0 0]])
          (fun x => ![xi x 1 2, -xi x 1 0]) (cmp E 1) (fun x t => ![H x t 2, -H x t 0])
          (fun x t => -Je x t 1) (fun x t => ![-Jm x t 2, Jm x t 0])) ∧
    (∀ (eO xi mu : Plane → Fin 3 → Fin 3 → ℝ) (E H Je Jm : Plane → ℝ → Fin 3 → ℝ),
      TMSystem eO xi mu E H Je Jm ↔
        UnifiedEqs (fun x => mu x 1 1)
          (fun x => ![![eO x 2 2, -eO x 2 0], ![-eO x 2 0, eO x 0 0]])
          (fun x => ![-xi x 2 1, xi x 0 1]) (cmp H 1) (fun x t => ![-E x t 2, E x t 0])
          (fun x t => -Jm x t 1) (fun x t => ![Je x t 2, -Je x t 0])) ∧
    (∀ (rhoO : Plane → Fin 3 → Fin 3 → ℝ) (xi : Plane → Fin 3 → Fin 3 → Fin 3 → ℝ)
        (s : Plane → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (v F : Plane → ℝ → Fin 3 → ℝ)
        (tau h : Plane → ℝ → Fin 3 → Fin 3 → ℝ),
      SHSystem rhoO xi s v tau F h ↔
        UnifiedEqs (fun x => rhoO x 1 1)
          (fun x => ![![4 * s x 0 1 1 0, 4 * s x 0 1 1 2], ![4 * s x 0 1 1 2, 4 * s x 2 1 1 2]])
          (fun x => ![2 * xi x 1 1 0, 2 * xi x 1 1 2]) (cmp v 1)
          (fun x t => ![-tau x t 1 0, -tau x t 1 2]) (cmp F 1)
          (fun x t => ![2 * h x t 1 0, 2 * h x t 1 2])) ∧
    (∀ (rhoO : Plane → Fin 3 → Fin 3 → ℝ) (xi : Plane → Fin 3 → ℝ) (kappa : Plane → ℝ)
        (v F : Plane → ℝ → Fin 3 → ℝ) (pr q : Plane → ℝ → ℝ),
      ACSystem rhoO xi kappa v pr F q ↔
        UnifiedEqs kappa (fun x => ![![rhoO x 0 0, rhoO x 2 0], ![rhoO x 2 0, rhoO x 2 2]])
          (fun x => ![xi x 0, xi x 2]) pr (fun x t => ![v x t 0, v x t 2]) q
          (fun x t => ![F x t 0, F x t 2])) := by sorry

end Arxiv1810_02867
