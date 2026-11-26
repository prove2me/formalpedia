-- Prove2me | Theorems.Thm_ClassNumberFormula_residue_of_factorization
-- name    : ClassNumberFormula.residue_of_factorization
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T03:50:28.24844+00:00
-- url     : https://prove2.me/theorems/df1e5e98-a453-57b6-87ae-80244e3bcee0
-- title:
--   Residue transport: the factorisation and $\chi\ne1$ give residue $L(1,\chi)$
-- statement:
--   Assume the factorisation $\zeta_K(s)=\zeta(s)L(s,\chi)$ for $\mathrm{Re}(s)>1$ and that $\chi$ is nontrivial. Then $(s-1)\zeta_K(s)\to L(1,\chi)$ as $s\to1$ through real $s>1$. For real $s>1$ the factorisation gives $(s-1)\zeta_K(s)=((s-1)\zeta(s))\,L(s,\chi)$; the first factor tends to $1$ (the residue of the Riemann zeta function at $s=1$) and the second tends to $L(1,\chi)$ because a nontrivial Dirichlet $L$-function is holomorphic, hence continuous, at $s=1$. The product of the two limits is $L(1,\chi)$, with no loss of constant.
-- source:
--   Mission 'Class Number Formula' (cc969585), milestone b3130a32 quadratic_dedekindZeta_eq_zeta_mul_L; Davenport, Multiplicative Number Theory, Ch. 6; Wikipedia 'Class number formula' rev 1366411311

import Mathlib
import Definitions.Def_ClassNumberFormula_Kronecker
open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology Real

namespace ClassNumberFormula

theorem residue_of_factorization (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [NeZero (discr K).natAbs]
    (χ : DirichletCharacter ℂ (discr K).natAbs)
    (hχ : ∀ n : ℕ, χ n = (kroneckerSymbol (discr K) n : ℂ))
    (hne : χ ≠ 1)
    (hfact : ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s) :
    Tendsto (fun s : ℝ => ((s : ℂ) - 1) * dedekindZeta K s) (𝓝[>] 1)
      (𝓝 (χ.LFunction 1)) := by sorry

end ClassNumberFormula
