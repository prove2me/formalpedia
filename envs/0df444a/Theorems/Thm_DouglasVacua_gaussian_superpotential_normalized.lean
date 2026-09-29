-- Prove2me | Theorems.Thm_DouglasVacua_gaussian_superpotential_normalized
-- name    : DouglasVacua.gaussian_superpotential_normalized
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:21:15.599608+00:00
-- url     : https://prove2.me/theorems/3386e79d-4fd5-4ab2-b15a-066260bfc5e8
-- title:
--   The complex Gaussian superpotential ensemble is unit normalised
-- statement:
--   For every $m\in\mathbb N$ and $\alpha>0$,
--   $$\int_{\mathbb C^m}\Big(\frac{\alpha}{\pi}\Big)^m\exp\Big(-\alpha\sum_{I=1}^m|w_I|^2\Big)\,d^{2m}w=1 ,$$
--   where $d^2w_I$ is Lebesgue measure on $\mathbb C\cong\mathbb R^2$. With $m=c(d,n)$ this is the statement that the weight $[d\mu(W)]$ on p. 35 is unit normalised; with $m=(n+1)(n+2)(n+3)/6$ it is $N(\alpha)=(\alpha/\pi)^m$ in (4.6). Only complex coefficients are considered (for real coefficients the constant $(\alpha/\pi)^m$ does not normalise).
-- source:
--   Michael R. Douglas, *The statistics of string/M theory vacua*, JHEP 05 (2003) 046, https://doi.org/10.1088/1126-6708/2003/05/046 (arXiv:hep-th/0303194). Section 4, p. 35 (weight $[d\mu(W)]$, "this is unit normalized"); Section 4.1, p. 37, eq. (4.6) and the formula for $N(\alpha)$.

import Mathlib
open Real MeasureTheory

namespace DouglasVacua

theorem gaussian_superpotential_normalized (m : ℕ) (α : ℝ) (hα : 0 < α) :
    ∫ w : Fin m → ℂ, (α / π) ^ m * Real.exp (-α * ∑ I, ‖w I‖ ^ 2) = 1 := by sorry

end DouglasVacua
