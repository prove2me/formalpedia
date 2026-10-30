-- Prove2me | Theorems.Thm_AggDiscountStopping_OneBarrier_harris_fkg_chebyshev
-- name    : AggDiscountStopping.OneBarrier.harris_fkg_chebyshev
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:02.596987+00:00
-- url     : https://prove2.me/theorems/789cdefe-54f9-4cd4-ac48-cffb8abeae53
-- title:
--   Proof of Theorem 4.8, p. 18 — Harris–FKG (Chebyshev) inequality ∫fh dμ ≤ ∫f dμ ∫h dμ for f decreasing, h increasing
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R$ concentrated on a set $S$ ($\mu(S^c)=0$), and let $f,h:\mathbb R\to\mathbb R$ be such that $f$ is decreasing on $S$ and $h$ is increasing on $S$. If $f$, $h$ and $fh$ are $\mu$-integrable, then
--   $$\int fh\,d\mu\le\int f\,d\mu\int h\,d\mu.$$
--
--   The proof of Theorem 4.8 applies this (the Harris–FKG inequality) with $\mu=F_\rho$, $S=[0,\infty)$, $f(r)=\phi'\big((K-a)\mathbb E[e^{-r\tau^x_a}]\big)(K-a)\mathbb E[e^{-r\tau^x_a}]$, decreasing in $r$, and $h(r)=-\frac1{K-a}+\partial_aH(r,a,x)$, increasing in $r$, to obtain the first inequality of the display on p. 18:
--   $$\frac{\partial\Lambda(x,a)}{\partial a}\le\Big(\int_0^\infty\phi'\big((K-a)\mathbb E[e^{-r\tau^x_a}]\big)(K-a)\mathbb E[e^{-r\tau^x_a}]dF_\rho(r)\Big)\times\Big(-\frac1{K-a}+\int_0^\infty\frac{\partial}{\partial a}H(r,a,x)dF_\rho(r)\Big).$$
--
--   **Formalization Note** Integrability of $f$, $h$ and $fh$ is stated explicitly; the Bochner integral is $0$ for non-integrable functions.
-- source:
--   Deng, Yu, Zhang, On time-consistent equilibrium stopping under aggregation of diverse discount rates, arXiv:2302.07470v4, proof of Theorem 4.8, Harris–FKG step, p. 18

import Mathlib
import Definitions.Def_AggDiscountStopping_OneBarrier_Setting

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace AggDiscountStopping.OneBarrier

theorem harris_fkg_chebyshev (μ : Measure ℝ) [IsProbabilityMeasure μ] (S : Set ℝ)
    (hS : μ Sᶜ = 0) (f h : ℝ → ℝ) (hf : AntitoneOn f S) (hh : MonotoneOn h S)
    (hfi : Integrable f μ) (hhi : Integrable h μ) (hfhi : Integrable (fun r => f r * h r) μ) :
    ∫ r, f r * h r ∂μ ≤ (∫ r, f r ∂μ) * (∫ r, h r ∂μ) := by sorry

end AggDiscountStopping.OneBarrier
