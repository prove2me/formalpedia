-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_equal_mode_amplitudes_large_N
-- name    : Arxivcond_mat_0004049.equal_mode_amplitudes_large_N
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T20:12:54.075887+00:00
-- url     : https://prove2.me/theorems/310e6765-6680-4212-a57a-4b108e77cc54
-- title:
--   Eq. (20): joint distribution of C_0 and C_1 for equal modes
-- statement:
--   Let $\gamma>0$, and consider equal incident and detected modes, $n=m$, so that $C_k=\sum_i\tau_i^ku_i^2$ (eq. (19)). As $N\to\infty$ the joint law of $c_0=N^{1/2}C_0$ and $c_1=C_1/(\gamma N)$ converges to the law on $\mathbb{C}^2$ with density (with respect to the real and imaginary parts) proportional to
--
--   $$\exp(-|c_0|^2/2)\int_0^\infty dx\,x^2e^{-x}\big(1+|c_1|^2x^2\big)^{-5/2}.$$
--
--   This is eq. (20), $P(C_0,C_1)\propto\exp(-N|C_0|^2/2)\int_0^\infty dx\,x^2e^{-x}\big(1+\frac{|C_1|^2x^2}{\gamma^2N^2}-\frac{2x}{\gamma N}\mathrm{Re}\,C_0C_1^*\big)^{-5/2}$, at leading order in $N$.
--
--   **Formalization Note** In these variables the cross term of eq. (20) is $2x\,\mathrm{Re}(c_0\bar c_1)/N^{1/2}$. It vanishes as $N\to\infty$, as the paper notes on p. 4. Eq. (20) is a large-$N$ result, and only its $N\to\infty$ limit has a precise meaning, so the statement is that limit. The normalisation is computed by the statement, since the paper gives only proportionality.
-- source:
--   Schomerus, van Bemmel and Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), claim c016; eqs. (19)-(20), PDF p. 3

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Filter Topology

namespace Arxivcond_mat_0004049

theorem equal_mode_amplitudes_large_N (γ : ℝ) (hγ : 0 < γ) :
    LawTendsto γ
      (fun N (ω : Sample N) => ((Real.sqrt N : ℂ) * ampC 0 ω, ampC 1 ω / ((γ * N : ℝ) : ℂ)))
      ((∫⁻ c : ℂ × ℂ, ENNReal.ofReal (eq20LimitWeight c.1 c.2))⁻¹ •
        (volume : Measure (ℂ × ℂ)).withDensity
          (fun c => ENNReal.ofReal (eq20LimitWeight c.1 c.2))) := by sorry

end Arxivcond_mat_0004049
