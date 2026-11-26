-- Prove2me | Theorems.Thm_ClassNumberFormula_quadratic_euler_factorization
-- name    : ClassNumberFormula.quadratic_euler_factorization
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T03:50:30.476074+00:00
-- url     : https://prove2.me/theorems/d76d43cb-57d6-5e23-a34d-1f209f3e0dc1
-- title:
--   Quadratic fields: Euler-factor transport gives $\zeta_K(s)=\zeta(s)L(s,\chi)$ for $\mathrm{Re}(s)>1$
-- statement:
--   Let $K$ be a quadratic number field, $d$ its discriminant, and $\chi$ the Dirichlet character modulo $|d|$ given by the Kronecker symbol. Then for every $s$ with $\mathrm{Re}(s)>1$, $\zeta_K(s)=\zeta(s)L(s,\chi)$. This is the Euler-product step: at each prime $p$ the local factor of $\zeta_K$ is $(1-p^{-s})^{-1}(1-\chi(p)p^{-s})^{-1}$, because $p$ splits, stays inert, or ramifies in $K$ exactly according as $\chi(p)=(d/p)$ is $1$, $-1$, or $0$, and the ideals above $p$ then have norms $p,p$, $p^2$, or $p$ respectively. Absolute convergence for $\mathrm{Re}(s)>1$ makes the product comparison legitimate, so the loss in this transport is zero.
-- source:
--   Mission 'Class Number Formula' (cc969585), milestone b3130a32 quadratic_dedekindZeta_eq_zeta_mul_L; Davenport, Multiplicative Number Theory, Ch. 6; Wikipedia 'Class number formula' rev 1366411311

import Mathlib
import Definitions.Def_ClassNumberFormula_Kronecker
open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology Real

namespace ClassNumberFormula

theorem quadratic_euler_factorization (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [NeZero (discr K).natAbs]
    (χ : DirichletCharacter ℂ (discr K).natAbs)
    (hχ : ∀ n : ℕ, χ n = (kroneckerSymbol (discr K) n : ℂ)) :
    ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s := by sorry

end ClassNumberFormula
