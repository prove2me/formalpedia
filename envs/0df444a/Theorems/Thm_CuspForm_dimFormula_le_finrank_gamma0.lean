-- Prove2me | Theorems.Thm_CuspForm_dimFormula_le_finrank_gamma0
-- name    : CuspForm.dimFormula_le_finrank_gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/1382ecca-b09e-5965-92e5-54fd6407c802
-- title:
--   Lower bound for dim S_k(Γ₀(N)), k≥ 4 even
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ and let $k$ be a natural number with $4 \le k$ and $k$ even. Write $\nu_2(N)$ for the number of $x \in \mathbb{Z}/N$ with $x^2 + 1 = 0$, $\nu_3(N)$ for the number of $x \in \mathbb{Z}/N$ with $x^2 + x + 1 = 0$, $\nu_\infty(N) = \sum_{d \mid N} \varphi(\gcd(d, N/d))$, and $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$; let $g(N) \in \mathbb{Q}$ be the rational number $1 + \psi(N)/12 - \nu_2(N)/4 - \nu_3(N)/3 - \nu_\infty(N)/2$. Then the inequality
--   $$(k-1)\bigl(g(N) - 1\bigr) + \lfloor k/4 \rfloor\, \nu_2(N) + \lfloor k/3 \rfloor\, \nu_3(N) + \bigl(k/2 - 1\bigr)\, \nu_\infty(N) \ \le\ \dim_{\mathbb{C}} S_k(\Gamma_0(N))$$
--   holds in $\mathbb{Q}$, where $\lfloor k/4 \rfloor$ and $\lfloor k/3 \rfloor$ denote the quotients of $k$ by $4$ and by $3$ in the natural numbers, cast to $\mathbb{Q}$, while $k/2$ is computed in $\mathbb{Q}$, and the right-hand side is the $\mathbb{C}$-dimension of the space of cusp forms of weight $k$ (viewed as an integer weight) for the congruence subgroup $\Gamma_0(N)$, cast to $\mathbb{Q}$.
--
--   The right-hand side is the classical dimension of $S_k(\Gamma_0(N))$ for even $k \ge 4$, and the left-hand side is the value predicted by the Riemann–Roch dimension formula expressed through the genus, elliptic-point and cusp numerics of $X_0(N)$; only the inequality ‘at least’ is asserted here, which is the half obtained from the Riemann inequality applied to an explicit divisor on the modular function field. It is used in the comparison of Eichler–Shimura and Hecke data ([`HeckeEis.isCompl_range_eichlerShimuraMap_range_conj`](thm.html#HeckeEis.isCompl_range_eichlerShimuraMap_range_conj)) and in the corresponding lower bound for spaces of mod $p$ cusp forms ([`ModPForms.dimFormulaCusp_le_finrank_modPCusp`](thm.html#ModPForms.dimFormulaCusp_le_finrank_modPCusp)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_dimFormula_le_finrank_gamma0.lean

import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.dimFormula_le_finrank_gamma0 (N : ℕ) [NeZero N] (k : ℕ) (hk : 4 ≤ k) (hke : Even k) :
    (((k : ℚ) - 1) * (ModularCurve.genusFormula N - 1) + ((k / 4 : ℕ) : ℚ) * (ModularCurve.nuTwo N : ℚ)
        + ((k / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ) + ((k : ℚ) / 2 - 1) * (ModularCurve.cuspCount N : ℚ))
      ≤ (Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) (k : ℤ)) : ℚ) := by sorry
