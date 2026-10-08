-- Prove2me | Theorems.Thm_ExtADMM_StrongCvx_spectral_radius
-- name    : ExtADMM.StrongCvx.spectral_radius
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:18.270725+00:00
-- url     : https://prove2.me/theorems/dbaa2476-a6a4-4c28-8a68-46ed07b08275
-- title:
--   p. 14, after (4.1) — the spectral radius of the iteration matrix of (1.5) on (4.1) with β = 1 is 1.0087
-- statement:
--   Let $M_{41}$ be the $5\times5$ iteration matrix of the direct extension of ADMM (1.5) with $\beta=1$ on the strongly convex instance (4.1). Its spectral radius, the largest modulus of a complex eigenvalue, equals $1.0087$ to four decimal places:
--
--   $$\rho(M_{41})=\max\{|d| : d\in\mathbb C,\ \det(dI-M_{41})=0\}\in[1.00865,\ 1.00875).$$
--
--   In particular $\rho(M_{41})>1$, which is what makes divergence possible: the iteration has an eigen-direction along which it expands.
--
--   **Formalization Note** Eigenvalues are taken as the complex roots of the characteristic polynomial of $M_{41}$ viewed as a complex matrix; the dominant eigenvalues of $M_{41}$ form a non-real conjugate pair, so a real-only formulation would miss them. The statement asserts a root $d$ of maximal modulus with $1.00865\le|d|<1.00875$, which is exactly "the spectral radius rounds to $1.0087$".
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), p. 14, after (4.1)

import Mathlib
import Definitions.Def_ExtADMM_StrongCvx_Setting
import Definitions.Def_ExtADMM_StrongCvx_Example41

namespace ExtADMM.StrongCvx

open Matrix

/-- p. 14, after (4.1): the spectral radius of the iteration matrix of (1.5) with `β = 1` on
(4.1) is `1.0087` (to four decimals). Eigenvalues are the complex roots of the characteristic
polynomial; there is a root `d` of maximal modulus with `1.00865 ≤ |d| < 1.00875`. -/
theorem spectral_radius :
    ∃ d : ℂ, ((M41.map (algebraMap ℝ ℂ)).charpoly).IsRoot d ∧ 1.00865 ≤ ‖d‖ ∧ ‖d‖ < 1.00875 ∧
      ∀ e : ℂ, ((M41.map (algebraMap ℝ ℂ)).charpoly).IsRoot e → ‖e‖ ≤ ‖d‖ := by sorry

end ExtADMM.StrongCvx
