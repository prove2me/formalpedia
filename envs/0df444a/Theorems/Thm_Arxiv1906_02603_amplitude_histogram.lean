-- Prove2me | Theorems.Thm_Arxiv1906_02603_amplitude_histogram
-- name    : Arxiv1906_02603.amplitude_histogram
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T06:41:29.663384+00:00
-- url     : https://prove2.me/theorems/ac5de35b-f9b2-45ad-925f-74c60241c4f3
-- title:
--   Eq. (8): the histogram of envelope amplitudes of the power-law vessel population
-- statement:
--   Let $N_0>0$, $A_0>0$, $a_{\min}\ge0$ and $b\in\mathbb{R}$. Vessels of radius $a>a_{\min}$ have number density $N[a]=N_0a^{-b}$ and produce echoes of amplitude $A[a]=A_0\sqrt{a-a_{\min}}$. Then:
--
--   1. for $a>a_{\min}$, the rule (7) $N[A]=N[a]/(dA/da)$ gives $N[A]=\dfrac{2N_0A}{A_0^2[(A/A_0)^2+a_{\min}]^b}$ at $A=A[a]$;
--   2. for $A>0$ the inverse is $a[A]=(A/A_0)^2+a_{\min}>a_{\min}$;
--   3. the measure $N_0a^{-b}\,da$ on $(a_{\min},\infty)$, pushed forward by $a\mapsto A[a]$, is the measure on $(0,\infty)$ with density
--
--   $$N[A]=\frac{2N_0A}{A_0^2\big[(A/A_0)^2+a_{\min}\big]^b}.$$
--
--   This is eq. (8), the paper's four-parameter histogram of envelope amplitudes.
--
--   **Formalization Note** The paper's "general theory of transformed distributions" (eq. (7), Appendix eq. (16)) is stated in item 3 as an identity of measures: the number of vessels whose amplitude falls in any Borel set equals the integral of $N[A]$ over that set.
-- source:
--   K. J. Parker, The first order statistics of backscatter from the fractal branching vasculature, arXiv:1906.02603v3 (2019), claim c003; Section II, eqs. (7)-(8), PDF p. 10

import Mathlib
import Definitions.Def_Arxiv1906_02603_Basic

open MeasureTheory Filter Topology Set

namespace Arxiv1906_02603

theorem amplitude_histogram (N0 A0 amin b : ℝ) (hN0 : 0 < N0) (hA0 : 0 < A0) (hamin : 0 ≤ amin) :
    (∀ a : ℝ, amin < a →
      vesselDensity N0 b a / deriv (amplitudeOfRadius A0 amin) a =
        ampHist N0 A0 amin b (amplitudeOfRadius A0 amin a)) ∧
    (∀ A : ℝ, 0 < A → amin < (A / A0) ^ 2 + amin ∧
      amplitudeOfRadius A0 amin ((A / A0) ^ 2 + amin) = A) ∧
    Measure.map (amplitudeOfRadius A0 amin)
        ((volume.restrict (Ioi amin)).withDensity
          (fun a => ENNReal.ofReal (vesselDensity N0 b a))) =
      (volume.restrict (Ioi 0)).withDensity (fun A => ENNReal.ofReal (ampHist N0 A0 amin b A)) := by sorry

end Arxiv1906_02603
