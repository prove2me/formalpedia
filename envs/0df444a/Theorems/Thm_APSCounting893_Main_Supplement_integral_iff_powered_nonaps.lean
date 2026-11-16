-- Prove2me | Theorems.Thm_APSCounting893_Main_Supplement_integral_iff_powered_nonaps
-- name    : APSCounting893.Main.Supplement.integral_iff_powered_nonaps
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:13:15.912989+00:00
-- url     : https://prove2.me/theorems/3f7ca69a-c39f-44d3-b926-2d948cc9e732
-- title:
--   Theorem 7.8 — Integrality iff the powered system has no APS
-- statement:
--   For complex polynomials $f,f_1,\ldots,f_m$, let $A=\mathbb C[f_i]$, $\rho=\operatorname{trdeg}_{\mathbb C}\mathbb C(f_i)$ and $\Delta=\max\{\deg f_i,\deg f+1\}$. For every integer $D\ge(\rho+2)\Delta^{\rho+1}$ set $M=D+1$ and $\Psi_M=(uf_1^M,\ldots,uf_m^M,u,1-uf)$, where $u$ is independent. Then
--
--   $$f\text{ integral over }A\quad\Longleftrightarrow\quad\Psi_M\text{ has no APS}.$$
--
--   The bound is computed from the data without an integrality assumption or a supplied certificate. Every powered generator and both last outputs occur. This is the companion theorem underlying the forward decision reduction.
--
--   Differences from the source:
--   - encoding: an integer D at least the displayed nonnegative bound → D is a natural number satisfying the same bound, and M=D+1; reason: the bound is positive, so this represents exactly all source integers in its stated range
--   - encoding: the powered tuple in C[x,u] → Fin (m+2) outputs and the last independent variable u; reason: the formula is u times fi to the power M, including zero targets and generators under the source conventions
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Theorem 7.8, p. 31

import Definitions.Def_APSCounting893_Main_Supplement_Certificates

set_option autoImplicit false

namespace APSCounting893.Main.Supplement

/-- Theorem 7.8: every D above the bound, defined independently of integrality. -/
theorem integral_iff_powered_nonaps (n m : ℕ) (F : PolynomialMap ℂ n m)
    (f : Polynomials ℂ n) (D : ℕ) (hD : certificateBound F f ≤ D) :
    IntegralOverGenerators F f ↔ ¬ hasAPS (poweredSystem F f (D + 1)) := by sorry

end APSCounting893.Main.Supplement
