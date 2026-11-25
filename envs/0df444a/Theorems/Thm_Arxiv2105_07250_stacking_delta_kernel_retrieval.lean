-- Prove2me | Theorems.Thm_Arxiv2105_07250_stacking_delta_kernel_retrieval
-- name    : Arxiv2105_07250.stacking_delta_kernel_retrieval
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:30:54.754405+00:00
-- url     : https://prove2.me/theorems/266452d6-0f26-414a-b66e-0e4db95efdfc
-- title:
--   Eqs. (8)-(9): a delta-correlated kernel gives the direct retrieval times the power spectrum
-- statement:
--   Let $\rho,c>0$ and let $G_A,G_B$ be such that $\overline{G_A}\,G_B$ is integrable over $S$. Suppose the stacking-average kernel satisfies (8) with proportionality constant $C>0$, that is, $\langle\hat F^*\hat F\rangle(x',x'')\,dx'dx''=C\,\delta(x'-x'')|\hat s(\omega)|^2\,dx'dx''$. Then the stacked retrieval (6) is
--
--   $$\langle\hat h(x_A,x_B,\omega)\rangle=C\,|\hat s(\omega)|^2\,\hat g(x_A,x_B,\omega),$$
--
--   which is eq. (9). If $\hat s(\omega)\ne0$, the phase of $\langle\hat h\rangle$ equals the phase of $\hat g$.
--
--   **Formalization Note** A delta kernel is not a function, so the stacking-average kernel enters (6) as a measure on $S\times S$. Eq. (8) then says that this measure is $C|\hat s|^2$ times arc length carried onto the diagonal. The paper's "$\propto$" is the positive constant $C$; the phase statement needs $C|\hat s|^2>0$, which the paper uses implicitly. Phase is $\arg$.
-- source:
--   D. Ayala-Garcia, A. Curtis and M. Branicki, Seismic Interferometry from Correlated Noise Sources, arXiv:2105.07250v2 (2021), claim c005; Section 3, eqs. (6)-(9) and the paragraph after (9), PDF p. 10

import Mathlib
import Definitions.Def_Arxiv2105_07250_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace Arxiv2105_07250

theorem stacking_delta_kernel_retrieval (ρ c : ℝ) (hρ : 0 < ρ) (hc : 0 < c) (GA GB : ℝ → ℂ)
    (hint : Integrable (fun x' : ℝ => starRingEnd ℂ (GA x') * GB x')) (s : ℂ) (C : ℝ) (hC : 0 < C) :
    stackedRetrievalOfKernel ρ c (ENNReal.ofReal C • deltaKernel s) GA GB =
        ((C * Complex.normSq s : ℝ) : ℂ) * directRetrieval ρ c GA GB ∧
      (s ≠ 0 → Complex.arg (stackedRetrievalOfKernel ρ c (ENNReal.ofReal C • deltaKernel s) GA GB) =
        Complex.arg (directRetrieval ρ c GA GB)) := by sorry

end Arxiv2105_07250
