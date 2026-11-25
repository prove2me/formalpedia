-- Prove2me | Theorems.Thm_ContrastiveDuality_criteria_trace_forms
-- name    : ContrastiveDuality.criteria_trace_forms
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T06:29:41.648796+00:00
-- url     : https://prove2.me/theorems/ab661f52-37ec-47a7-922f-1512f4164401
-- title:
--   Theorem C.4 (proof, eqs. (40)-(46)): trace forms of $L_{nc}$ and $L_c$
-- statement:
--   Let $\mathcal K\in\mathbb{R}^{M\times N}$ be any real matrix. Then the two criteria of Definition 3.2 have the trace forms
--
--   $$L_{nc}=\operatorname{tr}(\mathcal K^T\mathcal K\mathcal K^T\mathcal K)-\operatorname{tr}\big(\mathcal K\mathcal K^T\operatorname{diag}(\mathcal K\mathcal K^T)\big),\qquad L_c=\operatorname{tr}(\mathcal K^T\mathcal K\mathcal K^T\mathcal K)-\operatorname{tr}\big(\mathcal K^T\mathcal K\operatorname{diag}(\mathcal K^T\mathcal K)\big).$$
--
--   These are equations (44) and (46) of the proof of Theorem 3.3: both criteria share the term $\operatorname{tr}((\mathcal K^T\mathcal K)^2)=\operatorname{tr}((\mathcal K\mathcal K^T)^2)$ and differ only in the diagonal correction.
-- source:
--   Garrido, Chen, Bardes, Najman and LeCun, On the duality between contrastive and non-contrastive self-supervised learning, arXiv:2206.02574v3 (ICLR 2023), Appendix C, proof of Theorem C.4 (= Theorem 3.3), eqs. (40)-(44) and (45)-(46), p. 17

import Mathlib
import Definitions.Def_ContrastiveDuality_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace ContrastiveDuality

theorem criteria_trace_forms {M N : ℕ} (K : Matrix (Fin M) (Fin N) ℝ) :
    nonContrastiveCriterion K =
        Matrix.trace (Kᵀ * K * Kᵀ * K) - Matrix.trace (K * Kᵀ * extractedDiag (K * Kᵀ)) ∧
    contrastiveCriterion K =
        Matrix.trace (Kᵀ * K * Kᵀ * K) - Matrix.trace (Kᵀ * K * extractedDiag (Kᵀ * K)) := by sorry

end ContrastiveDuality
