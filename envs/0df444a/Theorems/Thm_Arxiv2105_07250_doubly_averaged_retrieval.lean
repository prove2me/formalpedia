-- Prove2me | Theorems.Thm_Arxiv2105_07250_doubly_averaged_retrieval
-- name    : Arxiv2105_07250.doubly_averaged_retrieval
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:33:40.94832+00:00
-- url     : https://prove2.me/theorems/a6129a86-3fa7-5e04-949d-455deb72ec70
-- title:
--   Eq. (26): stacking the random-window average multiplies the two kernels
-- statement:
--   Let $\rho,c,|v|,T>0$, and let $f_T$ be a probability density that vanishes outside a bounded interval. Let the source signature $F$ be a jointly measurable random field over a probability space of noise realisations, and let $G_A,G_B$ be measurable. Suppose Fubini's theorem applies, in the sense that $(\varpi,x',x'')\mapsto\overline{F_\varpi(x')G_A(x')}F_\varpi(x'')G_B(x'')$ is integrable. Then:
--
--   1. the random-windowing kernel is symmetric: $\langle\chi\chi\rangle_T(x',x'')=\langle\chi\chi\rangle_T(x'',x')$;
--   2. it is concentrated near the diagonal: $\langle\chi\chi\rangle_T(x',x'')=0$ whenever $|x'-x''|>2T|v|$;
--   3. stacking the averaged retrieval multiplies the two averaging kernels (eq. 26):
--   $$\langle\hat h_T(x_A,x_B,\omega)\rangle=\frac2{\rho c}\int_S\int_S\langle\hat F^*\hat F\rangle(x',x'')\,\langle\chi\chi\rangle_T(x',x'')\,\hat G^*(x_A,x',\omega)\,\hat G(x_B,x'',\omega)\,dx''\,dx'.$$
--
--   **Formalization Note** The independence of stacking and window randomisation is built in: the window average is taken inside each realisation and the stacking average outside. The paper's standing assumption "Fubini's theorem is satisfied" is the integrability hypothesis. Eq. (26) as printed has $\hat G^*(x,x')\hat G(x,x'')$ with a single receiver $x$; the receivers $x_A$ and $x_B$ are meant. The paper's "for $T\ll1$ the kernel concentrates the integrand within an $\mathcal O(T|v|)$ neighbourhood of $x'=x''$" is stated in item 2 as the exact support bound $2T|v|$, which holds for every $T>0$. The assertion that the doubly averaged retrieval "will lead to an improved retrieval" is not a mathematical statement and is not included.
-- source:
--   D. Ayala-Garcia, A. Curtis and M. Branicki, Seismic Interferometry from Correlated Noise Sources, arXiv:2105.07250v2 (2021), claim c031; Section 4.1, eqs. (22)-(24), the paragraph after eq. (25), and eq. (26) with the following paragraph, PDF pp. 19-21

import Mathlib
import Definitions.Def_Arxiv2105_07250_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace Arxiv2105_07250

theorem doubly_averaged_retrieval {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ρ c : ℝ) (hρ : 0 < ρ) (hc : 0 < c) (F : Ω → ℝ → ℂ)
    (hF : Measurable (Function.uncurry F)) (GA GB : ℝ → ℂ) (hGA : Measurable GA)
    (hGB : Measurable GB)
    (hfub : Integrable (fun q : Ω × ℝ × ℝ =>
      starRingEnd ℂ (F q.1 q.2.1 * GA q.2.1) * (F q.1 q.2.2 * GB q.2.2))
      (P.prod (volume.prod volume)))
    (vabs T : ℝ) (hv : 0 < vabs) (hT : 0 < T) (fT : ℝ → ℝ) (hf : IsWindowDensity fT) :
    (∀ x' x'' : ℝ, windowKernel fT vabs T x' x'' = windowKernel fT vabs T x'' x') ∧
    (∀ x' x'' : ℝ, 2 * T * vabs < |x' - x''| → windowKernel fT vabs T x' x'' = 0) ∧
    ∫ r, averagedRetrieval ρ c fT (F r) GA GB vabs T ∂P =
      ((2 / (ρ * c) : ℝ) : ℂ) * ∫ x', ∫ x'', stackKernel P F x' x'' *
        (windowKernel fT vabs T x' x'' : ℂ) * (starRingEnd ℂ (GA x') * GB x'') := by sorry

end Arxiv2105_07250
