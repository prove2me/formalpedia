-- Prove2me | Theorems.Thm_CuspForm_finrank_gamma0_weight_two_eq_genusFormula
-- name    : CuspForm.finrank_gamma0_weight_two_eq_genusFormula
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/4569a0dc-12f1-5e43-bb44-136723fc089d
-- title:
--   dim_ℂ S₂(Γ₀(N)) equals the genus formula
-- statement:
--   Let $N$ be a natural number, assumed nonzero (the typeclass `[NeZero N]`). Consider Mathlib's space `CuspForm (CongruenceSubgroup.Gamma0 N) 2` of weight-$2$ cusp forms for the congruence subgroup $\Gamma_0(N)$, and let $\dim_{\mathbb C}$ denote its `Module.finrank` over $\mathbb C$. The assertion is that this dimension, viewed as a rational number, equals the rational quantity [`ModularCurve.genusFormula N`](def/ModularCurve_GenusNumerics.html#L20), namely
--   $$1+\frac{\psi(N)}{12}-\frac{\nu_2(N)}{4}-\frac{\nu_3(N)}{3}-\frac{\nu_\infty(N)}{2},$$
--   where the four arithmetic inputs are defined as follows: $\psi(N)=\sum_{d\mid N,\ d\ \text{squarefree}} N/d$ (`dedekindPsi`); $\nu_2(N)$ is the number of elements $x$ of $\mathbb Z/N$ with $x^2+1=0$ (`nuTwo`, a `Nat.card` of the corresponding subtype); $\nu_3(N)$ is the number of $x\in\mathbb Z/N$ with $x^2+x+1=0$ (`nuThree`); and $\nu_\infty(N)=\sum_{d\mid N}\varphi(\gcd(d,N/d))$ (`cuspCount`), the sum being over the divisors of $N$ with $\varphi$ Euler's totient. In particular the right-hand side is a purely elementary arithmetic function of $N$, and the equality holds in $\mathbb Q$.
--
--   This is the weight-$2$ dimension formula for $\Gamma_0(N)$: it combines the Eichler–Shimura identification of $S_2(\Gamma_0(N))$ with the holomorphic differentials on $X_0(N)$ with the Riemann–Hurwitz computation of the genus of $X_0(N)$, expressed here through the elementary quantities $\psi$, $\nu_2$, $\nu_3$ and $\nu_\infty$. It feeds the comparisons between cusp forms, regular differentials and the integral lattice of $q$-expansions on $X_0(N)$, and the torsion bound [`ModularCurve.JZero.pow_two_mul_genusFF_le_card_torsion`](thm.html#ModularCurve.JZero.pow_two_mul_genusFF_le_card_torsion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_finrank_gamma0_weight_two_eq_genusFormula.lean

import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.finrank_gamma0_weight_two_eq_genusFormula (N : ℕ) [NeZero N] :
    (Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) : ℚ) = ModularCurve.genusFormula N := by sorry
