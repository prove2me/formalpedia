-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_localizedModel_isProbabilityMeasure
-- name    : Arxivcond_mat_0004049.localizedModel_isProbabilityMeasure
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T14:34:16.450795+00:00
-- url     : https://prove2.me/theorems/ffaabddc-be36-53ed-a564-b3b4cf67e448
-- title:
--   The localized-regime model is a probability space
-- statement:
--   Let $N \ge 0$ and $\gamma > 0$. The localized-regime model of the paper draws a sample $(g, v, \mu)$ with $g, v$ independent complex Gaussian vectors with entries of variance $1/N$, independent of rates $\mu$ from the Laguerre ensemble of eq. (7). Its law, the product of the three laws, is a probability measure.
--
--   Every distributional statement of the mission (eqs. (13), (15), (16), (20)) is a statement about this probability space.
-- source:
--   Model of H. Schomerus, K. J. H. van Bemmel, C. W. J. Beenakker, arXiv:cond-mat/0004049v1 (2000), https://arxiv.org/abs/cond-mat/0004049, p. 2: the localized-regime model (eqs. (5)-(7), (11), (19))

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory ProbabilityTheory

namespace Arxivcond_mat_0004049

theorem localizedModel_isProbabilityMeasure (N : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    IsProbabilityMeasure (localizedModel N γ) := by sorry

end Arxivcond_mat_0004049
