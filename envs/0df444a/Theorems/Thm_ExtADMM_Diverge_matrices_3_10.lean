-- Prove2me | Theorems.Thm_ExtADMM_Diverge_matrices_3_10
-- name    : ExtADMM.Diverge.matrices_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:06:02.865982+00:00
-- url     : https://prove2.me/theorems/7729a6e4-19a6-469a-acbf-a4c1a3cf8550
-- title:
--   L, R and M = L⁻¹R for (3.10), p. 12 — the 5 × 5 matrices of the example, entry by entry
-- statement:
--   For the data
--
--   $$A=(A_1,A_2,A_3)=\begin{pmatrix}1&1&1\\1&1&2\\1&2&2\end{pmatrix}\qquad(3.10),$$
--
--   the matrices $L$ of (3.6) and $R$ of (3.7) are
--
--   $$L=\begin{pmatrix}6&0&0&0&0\\7&9&0&0&0\\1&1&1&0&0\\1&2&0&1&0\\2&2&0&0&1\end{pmatrix},\qquad R=\frac13\begin{pmatrix}16&-1&-1&-1&2\\20&25&-2&1&1\\4&5&2&-1&-1\\4&5&-1&2&-1\\4&5&-1&-1&2\end{pmatrix},$$
--
--   $\det L=54$, and
--
--   $$M=L^{-1}R=\frac{1}{162}\begin{pmatrix}144&-9&-9&-9&18\\8&157&-5&13&-8\\64&122&122&-58&-64\\56&-35&-35&91&-56\\-88&-26&-26&-62&88\end{pmatrix}.$$
--
--   This pins every printed entry of the example's iteration matrix, which is the object of the spectral and divergence statements that follow.
--
--   **Formalization Note.** $A_i$ are the *columns* of (3.10): $A_1=(1,1,1)^T$, $A_2=(1,1,2)^T$, $A_3=(1,2,2)^T$. The determinant is stated so that $L^{-1}$ is the genuine inverse rather than Mathlib's junk value for singular matrices.
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), p. 12, (3.10) and the matrices L, R, M = L⁻¹R

import Mathlib
import Definitions.Def_ExtADMM_Diverge_Setting

open Matrix Filter Topology

namespace ExtADMM.Diverge

/-- p. 12. At the data (3.10), the matrices `L` of (3.6) and `R` of (3.7) are the printed
`L310` and `R310`; `L310` is nonsingular (`det = 54`) and `M = L⁻¹R` is the printed `M310`. -/
theorem matrices_3_10 :
    Lmat a310_2 a310_3 = L310 ∧ Rmat a310_1 a310_2 a310_3 = R310 ∧
      L310.det = 54 ∧ L310⁻¹ * R310 = M310 := by sorry

end ExtADMM.Diverge
