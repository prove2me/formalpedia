-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_gaussVec_isProbabilityMeasure
-- name    : Arxivcond_mat_0004049.gaussVec_isProbabilityMeasure
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T14:34:05.812248+00:00
-- url     : https://prove2.me/theorems/753835e5-191e-40a1-bbbc-ed9bea35b86f
-- title:
--   The complex Gaussian vector of the model is a probability measure
-- statement:
--   Let $N \ge 0$. The complex Gaussian vector of p. 2 is $g = (g_1,\dots,g_N)$ with independent circular complex Gaussian entries of variance $\mathbb{E}|g_i|^2 = 1/N$ (real and imaginary parts independent with variance $1/(2N)$).
--
--   Its law on $\mathbb{C}^N$ is a probability measure.
--
--   The law is built as the image of a product of real Gaussian laws under the identification $\mathbb{R}^2 \cong \mathbb{C}$; this lemma records that it has total mass one.
-- source:
--   Model of H. Schomerus, K. J. H. van Bemmel, C. W. J. Beenakker, arXiv:cond-mat/0004049v1 (2000), https://arxiv.org/abs/cond-mat/0004049, p. 2: the Gaussian columns ("independent Gaussian random numbers with vanishing mean and variance $N^{-1}$")

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory ProbabilityTheory

namespace Arxivcond_mat_0004049

theorem gaussVec_isProbabilityMeasure (N : ℕ) :
    IsProbabilityMeasure (gaussVec N) := by sorry

end Arxivcond_mat_0004049
