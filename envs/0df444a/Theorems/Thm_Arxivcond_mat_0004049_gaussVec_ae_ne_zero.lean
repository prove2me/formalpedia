-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_gaussVec_ae_ne_zero
-- name    : Arxivcond_mat_0004049.gaussVec_ae_ne_zero
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T14:34:10.061555+00:00
-- url     : https://prove2.me/theorems/397f6635-d297-573a-95bc-2e2aa59f64ab
-- title:
--   The complex Gaussian vector is almost surely nonzero
-- statement:
--   Let $N \ge 1$. The complex Gaussian vector of p. 2 is $g = (g_1,\dots,g_N)$ with independent circular complex Gaussian entries of variance $\mathbb{E}|g_i|^2 = 1/N$ (real and imaginary parts independent with variance $1/(2N)$).
--
--   Then $g \ne 0$ almost surely:
--
--   $$
--   \mathbb{P}(g = 0) = 0 .
--   $$
--
--   Consequently the incident column $u = g/\|g\|_2$ is almost surely a well-defined unit vector, the law of a column of a Haar-distributed unitary matrix.
-- source:
--   Model of H. Schomerus, K. J. H. van Bemmel, C. W. J. Beenakker, arXiv:cond-mat/0004049v1 (2000), https://arxiv.org/abs/cond-mat/0004049, p. 2: the incident column u = g/‖g‖ ("a column of a matrix U uniformly distributed in the unitary group")

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory ProbabilityTheory

namespace Arxivcond_mat_0004049

theorem gaussVec_ae_ne_zero (N : ℕ) (hN : 1 ≤ N) :
    ∀ᵐ g ∂(gaussVec N), g ≠ 0 := by sorry

end Arxivcond_mat_0004049
