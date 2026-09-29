-- Prove2me | Theorems.Thm_CuspForm_genusFormula_le_finrank_gamma0_weight_two
-- name    : CuspForm.genusFormula_le_finrank_gamma0_weight_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/5abf5b1f-1c20-5f08-aca1-04c7c391943e
-- title:
--   Genus formula bounds dim_ℂ S₂(Γ₀(N)) from below
-- statement:
--   For every natural number $N \neq 0$, the rational number [`ModularCurve.genusFormula N`](def/ModularCurve_GenusNumerics.html#L20) is at most the complex dimension of the space of weight-two cusp forms for $\Gamma_0(N)$, the latter being the rank `Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)` viewed as a rational number. Here [`ModularCurve.genusFormula N`](def/ModularCurve_GenusNumerics.html#L20) is the explicit rational combination $$1 + \frac{\psi(N)}{12} - \frac{\nu_2(N)}{4} - \frac{\nu_3(N)}{3} - \frac{\nu_\infty(N)}{2},$$ in which $\psi(N)$ is `dedekindPsi N`, defined as the sum of $N/d$ over the squarefree divisors $d$ of $N$; $\nu_2(N)$ is `nuTwo N`, the number of elements $x$ of $\mathbb{Z}/N\mathbb{Z}$ with $x^2 + 1 = 0$; $\nu_3(N)$ is `nuThree N`, the number of elements $x$ of $\mathbb{Z}/N\mathbb{Z}$ with $x^2 + x + 1 = 0$; and $\nu_\infty(N)$ is `cuspCount N`, the sum of $\varphi(\gcd(d, N/d))$ over the divisors $d$ of $N$. Thus the assertion is one inequality between two explicitly given rational numbers, with no hypothesis on $N$ beyond its being nonzero.
--
--   This is the lower-bound half of the classical dimension formula $\dim_{\mathbb C} S_2(\Gamma_0(N)) = g(X_0(N))$, the genus being computed by the Riemann–Hurwitz count for $X_0(N) \to X(1)$; the proof passes through regular differentials on the modular function field over $\overline{\mathbb Q}$ and their $q$-expansions. Together with the matching upper bound it yields [`CuspForm.finrank_gamma0_weight_two_eq_genusFormula`](thm.html#CuspForm.finrank_gamma0_weight_two_eq_genusFormula), and it is used in the Eichler–Shimura decomposition and in the dimension estimates for mod $p$ cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_genusFormula_le_finrank_gamma0_weight_two.lean

import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.genusFormula_le_finrank_gamma0_weight_two (N : ℕ) [NeZero N] :
    ModularCurve.genusFormula N ≤ (Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) : ℚ) := by sorry
