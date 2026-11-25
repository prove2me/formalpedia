-- Prove2me | Theorems.Thm_Arxiv2105_07250_uniform_window_moments_and_tent
-- name    : Arxiv2105_07250.uniform_window_moments_and_tent
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T09:32:26.809917+00:00
-- url     : https://prove2.me/theorems/f0713d78-79ab-550f-b2fa-f9daded55ac3
-- title:
--   Eqs. (27)-(28) (as proved): uniform window centres and the tent kernel
-- statement:
--   Let $T>0$, $t_0\in\mathbb{R}$ and $v\in\mathbb{R}^2\setminus\{0\}$, and let the window centre $t_n$ be uniform on $D=[t_0-T,t_0+T]$, with density $f_T=\frac1{2T}$ on $D$ (eq. 27). Then $\int f_T=1$, $\langle t_n\rangle_T=t_0$, $\mathrm{Var}(t_n)=\langle(t_n-t_0)^2\rangle_T=T^2/3$, and $\langle x_n\rangle_T=vt_0=x_0$ for $x_n=t_nv$.
--
--   With $L=T|v|$, the convolution of two boxcars of height one and width $L$, evaluated at the source-location discrepancy $d=|x'-x''|$, is the right-hand side of (28):
--
--   $$\int_{\mathbb{R}}\mathbf 1_{[-L/2,L/2]}(y)\,\mathbf 1_{[-L/2,L/2]}(d-y)\,dy=(d+L)\Theta(d+L)+(d-L)\Theta(d-L)-2d\,\Theta(d).$$
--
--   This is the tent $\max(L-|x'-x''|,0)$, with height $T|v|$ and width $2T|v|$ (Figure 8).
--
--   **Formalization Note** The paper equates (28) with the random-windowing kernel (24) for uniform $f_T$. That identity is false: (24) is a probability, equal to $1$ at $x'=x''=x_0$, while (28) equals $T|v|$ there. The paper's only justification of (28) is that it "corresponds to the convolution of two boxcar functions of constant height one and width $T|v|$". The statement gives that computation and the shape of the tent, whose support is $|x'-x''|\le T|v|$, not the $2T|v|$ stated in the text (see REPORT.md).
-- source:
--   D. Ayala-Garcia, A. Curtis and M. Branicki, Seismic Interferometry from Correlated Noise Sources, arXiv:2105.07250v2 (2021), claim c014; Section 4.2, eqs. (27)-(28) and the following paragraphs, PDF pp. 21-22; Figure 8 caption, PDF p. 22

import Mathlib
import Definitions.Def_Arxiv2105_07250_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace Arxiv2105_07250

theorem uniform_window_moments_and_tent (t0 T : ℝ) (hT : 0 < T) (v : Plane) (hv : v ≠ 0) :
    (∫ τ, uniformWindowDensity t0 T τ) = 1 ∧
    windowAvg (uniformWindowDensity t0 T) (fun τ => τ) = t0 ∧
    windowAvg (uniformWindowDensity t0 T) (fun τ => (τ - t0) ^ 2) = T ^ 2 / 3 ∧
    windowAvg (uniformWindowDensity t0 T) (fun τ => τ • v) = t0 • v ∧
    (∀ x' x'' : ℝ, ∫ y, boxcar (T * ‖v‖) y * boxcar (T * ‖v‖) (|x' - x''| - y) =
      tentKernel (T * ‖v‖) |x' - x''|) ∧
    (∀ x' x'' : ℝ, tentKernel (T * ‖v‖) |x' - x''| = max (T * ‖v‖ - |x' - x''|) 0) := by sorry

end Arxiv2105_07250
