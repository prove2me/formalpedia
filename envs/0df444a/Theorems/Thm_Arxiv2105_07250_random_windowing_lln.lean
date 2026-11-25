-- Prove2me | Theorems.Thm_Arxiv2105_07250_random_windowing_lln
-- name    : Arxiv2105_07250.random_windowing_lln
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:33:04.656571+00:00
-- url     : https://prove2.me/theorems/4c71fded-85db-55ba-a0ab-0ed09a1740be
-- title:
--   Eq. (29): the empirical random-window mean converges to the averaged retrieval
-- statement:
--   Let $\rho,c,|v|,T>0$, and let $F,G_A,G_B$ be such that $FG_A$ and $FG_B$ are integrable over $S$ (one recording). Let $f_T$ be a probability density that vanishes outside a bounded interval, has mean $t_0$ and finite second moment $\int\tau^2f_T(\tau)\,d\tau<\infty$. If the window centres $t_1,t_2,\dots$ are independent with density $f_T$, then almost surely
--
--   $$\frac1N\sum_{n=1}^N\hat h(x_A,x_B,\omega;T,t_n)\xrightarrow[N\to\infty]{}\hat h_T(x_A,x_B,\omega).$$
--
--   **Formalization Note** The paper says only that the empirical mean "converges" by the law of large numbers, without naming the mode; almost-sure convergence (the strong law) is stated. The integrability of $FG_A$ and $FG_B$ is the condition under which the recordings (3) and (20) exist; it makes the windowed retrieval a bounded function of $t_n$. The paper's finite-variance condition is kept as printed, although REPORT.md notes that it is not the condition the law of large numbers needs. The claim that the procedure needs neither the speed $v$ nor a moving source is not a mathematical statement and is not included.
-- source:
--   D. Ayala-Garcia, A. Curtis and M. Branicki, Seismic Interferometry from Correlated Noise Sources, arXiv:2105.07250v2 (2021), claim c015; Section 4.3, eq. (29) and the following paragraph, PDF p. 24

import Mathlib
import Definitions.Def_Arxiv2105_07250_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace Arxiv2105_07250

theorem random_windowing_lln {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ρ c : ℝ) (hρ : 0 < ρ) (hc : 0 < c) (F GA GB : ℝ → ℂ)
    (hFA : Integrable (fun x' : ℝ => F x' * GA x')) (hFB : Integrable (fun x' : ℝ => F x' * GB x'))
    (vabs T t0 : ℝ) (hv : 0 < vabs) (hT : 0 < T) (fT : ℝ → ℝ) (hf : IsWindowDensity fT)
    (hmean : ∫ τ, τ * fT τ = t0) (hvar : Integrable (fun τ : ℝ => τ ^ 2 * fT τ))
    (t : ℕ → Ω → ℝ) (ht : ∀ n, Measurable (t n))
    (hlaw : ∀ n, P.map (t n) = volume.withDensity (fun τ => ENNReal.ofReal (fT τ)))
    (hind : iIndepFun t P) :
    ∀ᵐ r ∂P, Tendsto (fun N : ℕ => (1 / (N : ℂ)) *
        ∑ n ∈ Finset.range N, windowedRetrieval ρ c F GA GB vabs T (t n r)) atTop
      (𝓝 (averagedRetrieval ρ c fT F GA GB vabs T)) := by sorry

end Arxiv2105_07250
