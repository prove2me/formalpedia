-- Prove2me | Theorems.Thm_FlexCommitRO_BoxExt_valueR_box_eq_valueR_ext
-- name    : FlexCommitRO.BoxExt.valueR_box_eq_valueR_ext
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:00:33.58228+00:00
-- url     : https://prove2.me/theorems/70a66642-c030-4a8c-95da-b965154d6a11
-- title:
--   Proof of Proposition 1, pp. 270–271 — for every R the R-boxed RSFC problem has the same value on the demand box and on its extreme demands
-- statement:
--   Let an instance of the RSFC model be given, together with demand bounds $d_t^{\min} < d_t^{\max}$, $t = 1,\dots,T$, and let $R \in \mathbb R$. Write $\operatorname{value}_R(\mathcal U)$ for the optimal value of the min-max RSFC problem (5)–(6) over $\mathcal U^T = \mathcal U_1 \times \dots \times \mathcal U_T$ with the additional constraints that every decision has absolute value at most $R$. Then
--   $$
--   \operatorname{value}_R\big([d_1^{\min}, d_1^{\max}] \times \dots \times [d_T^{\min}, d_T^{\max}]\big) = \operatorname{value}_R\big(\{d_1^{\min}, d_1^{\max}\} \times \dots \times \{d_T^{\min}, d_T^{\max}\}\big).
--   $$
--
--   In the paper this is the rewriting of $(P)$ and $(P_+)$, with box constraints, as $(P[D_0,\dots,D_T])$ and $(P[\operatorname{ext}(D_0),\dots,\operatorname{ext}(D_T)])$, followed by Lemma 2.
--
--   **Formalization Note** The box bounds inventories, orders, cumulative orders, $y_t$, $u_t$, $w_t$ and $z_t$ — the components of the Appendix's stage vectors $s_t$. The Appendix's encoding puts $y_{t+1}$ in $s_{t+1}$, a function of $d^t$, whereas (6) makes $y_t$ a function of $d^{t-1}$; the statement is about (6) as printed, which a stage encoding keeping $y_t$ in $s_t$ also brings into the form of Lemma 2. Lean periods are 0-based.
-- source:
--   Ben-Tal, Golany, Nemirovski & Vial, Retailer-supplier flexible commitments contracts: a robust optimization approach, MSOM 7(3) (2005), pp. 270–271, Appendix, proof of Proposition 1 (continued)

import Mathlib
import Definitions.Def_FlexCommitRO_BoxExt_Setting

namespace FlexCommitRO.BoxExt

theorem valueR_box_eq_valueR_ext {T : ℕ} (D : RSFCData T) (dmin dmax : Fin T → ℝ)
    (hlt : ∀ t, dmin t < dmax t) (R : ℝ) :
    valueR D (fun t => Set.Icc (dmin t) (dmax t)) R =
      valueR D (fun t => ({dmin t, dmax t} : Set ℝ)) R := by sorry

end FlexCommitRO.BoxExt
