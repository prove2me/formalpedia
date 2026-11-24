-- Prove2me | Theorems.Thm_CSOffTheGrid_system_matrix_bounds
-- name    : CSOffTheGrid.system_matrix_bounds
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T03:25:46.19465+00:00
-- url     : https://prove2.me/theorems/1c0c43c5-2295-48ee-a0eb-41db9c03ffe2
-- title:
--   Proposition 4.1: the deterministic system matrix is near the identity
-- statement:
--   Let $M\ge2$, let $f_1,\dots,f_s\in[0,1]$ satisfy $\Delta_f\ge1/M$, and let $\bar D$ be the $2s\times2s$ system matrix
--
--   $$\bar D=\begin{bmatrix}\bar D_0&\frac1{\sqrt{|\bar K_M''(0)|}}\bar D_1\\-\frac1{\sqrt{|\bar K_M''(0)|}}\bar D_1&-\frac1{|\bar K_M''(0)|}\bar D_2\end{bmatrix},\qquad[\bar D_\ell]_{jk}=\bar K_M^{(\ell)}(f_j-f_k),$$
--
--   of the squared Fejér kernel $\bar K_M(f)=\big[\frac{\sin(\pi Mf)}{M\sin(\pi f)}\big]^4$. Then $\bar D$ is invertible and, in operator norm,
--
--   $$\|I-\bar D\|\le0.3623,\qquad\|\bar D\|\le1.3623,\qquad\|\bar D^{-1}\|\le1.568.$$
--
--   **Formalization Note** This is the printed statement, with $M\ge2$ added: for $M=1$ the paper's quantities are undefined, since $\bar K_1''(0)=0$. The paper's proof cites estimates of Candès and Fernandez-Granda that are proved only for $M\ge65$ and $\Delta_f\ge1/(M-1)$, so the paper does not prove the full range stated here. Numerically the bounds hold with a wide margin ($\|I-\bar D\|\le0.04$ in all configurations tested, $M=2,\dots,100$).
-- source:
--   Tang, Bhaskar, Shah and Recht, Compressed Sensing Off the Grid, arXiv:1207.6053v3 (2013), Section 4.1, Proposition 4.1, eqs. (4.6)-(4.9), p. 17; proof in Appendix C, p. 42, citing Candès and Fernandez-Granda (arXiv:1203.5871), eqs. (2.14)-(2.16)

import Mathlib
import Definitions.Def_CSOffTheGrid_Basic

open MeasureTheory
open scoped ENNReal ComplexOrder

namespace CSOffTheGrid

theorem system_matrix_bounds (M : ℕ) (hM : 2 ≤ M) {s : ℕ} (f : Fin s → ℝ)
    (hf : ∀ k, f k ∈ Set.Icc (0 : ℝ) 1) (hsep : IsSeparated f (1 / (M : ℝ))) :
    (sysMatBar M f).det ≠ 0 ∧ opNorm (1 - sysMatBar M f) ≤ 0.3623 ∧
      opNorm (sysMatBar M f) ≤ 1.3623 ∧ opNorm (sysMatBar M f)⁻¹ ≤ 1.568 := by sorry

end CSOffTheGrid
