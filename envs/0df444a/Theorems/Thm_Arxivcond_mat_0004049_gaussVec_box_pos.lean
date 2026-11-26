-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_gaussVec_box_pos
-- name    : Arxivcond_mat_0004049.gaussVec_box_pos
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T14:34:02.556177+00:00
-- url     : https://prove2.me/theorems/23777ef4-0776-5022-aeb9-a4dea3137f0a
-- title:
--   The complex Gaussian vector charges every open box
-- statement:
--   Let $N \ge 1$. The complex Gaussian vector of p. 2 is $g = (g_1,\dots,g_N)$ with independent circular complex Gaussian entries of variance $\mathbb{E}|g_i|^2 = 1/N$ (real and imaginary parts independent with variance $1/(2N)$). Let $c \in \mathbb{C}^N$ and $\delta > 0$. Then the box of half-width $\delta$ around $c$ has positive probability:
--
--   $$
--   \mathbb{P}\big(|\operatorname{Re}(g_j - c_j)| < \delta \text{ and } |\operatorname{Im}(g_j - c_j)| < \delta \text{ for all } j\big) > 0 .
--   $$
--
--   This is the tool for showing that events such as $A_0 \ne 0$ have positive probability by exhibiting an explicit box inside them.
-- source:
--   Model of H. Schomerus, K. J. H. van Bemmel, C. W. J. Beenakker, arXiv:cond-mat/0004049v1 (2000), https://arxiv.org/abs/cond-mat/0004049, p. 2: the detected column v ("independent Gaussian random numbers with vanishing mean and variance $N^{-1}$")

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory ProbabilityTheory

namespace Arxivcond_mat_0004049

theorem gaussVec_box_pos (N : ℕ) (hN : 1 ≤ N) (c : Fin N → ℂ) (δ : ℝ) (hδ : 0 < δ) :
    gaussVec N {v | ∀ j, |(v j - c j).re| < δ ∧ |(v j - c j).im| < δ} ≠ 0 := by sorry

end Arxivcond_mat_0004049
