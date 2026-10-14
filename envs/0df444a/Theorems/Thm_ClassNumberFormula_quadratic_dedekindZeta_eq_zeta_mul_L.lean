-- Prove2me | Theorems.Thm_ClassNumberFormula_quadratic_dedekindZeta_eq_zeta_mul_L
-- name    : ClassNumberFormula.quadratic_dedekindZeta_eq_zeta_mul_L
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T12:55:51.876647+00:00
-- url     : https://prove2.me/theorems/b3130a32-c995-4da3-a1ca-86c254948114
-- title:
--   Quadratic fields: $\zeta_K(s)=\zeta(s)L(s,\chi)$, and the residue is $L(1,\chi)$
-- statement:
--   Let $K$ be a quadratic number field with discriminant $d = D_K$, and let $\chi$ be the Dirichlet character modulo $|d|$ given by the Kronecker symbol, $\chi(n) = \left(\frac{d}{n}\right)$. Then:
--
--   1. for every $s$ with $\operatorname{Re}(s) > 1$,
--   $$\zeta_K(s) = \zeta(s)\,L(s,\chi);$$
--   2. the residue of $\zeta_K$ at $s = 1$ is $L(1,\chi)$:
--   $$\lim_{s\to1^+}(s-1)\,\zeta_K(s) = L(1,\chi).$$
--
--   Together with the general residue formula, this is how Dirichlet's class number formula appears as a special case of the class number formula.
--
--   **Formalization Note** $\zeta$ is Mathlib's `riemannZeta` and $L(s,\chi)$ is `DirichletCharacter.LFunction`, the analytic continuation; for the nontrivial character $\chi$ its value at $s=1$ is the value of the continuation. The instance argument `[NeZero |d|]` only records $d \neq 0$, which always holds.
-- source:
--   Wikipedia, "Class number formula" (revision oldid=1366411311), https://en.wikipedia.org/w/index.php?title=Class_number_formula&oldid=1366411311, section "Dirichlet class number formula" ("for a quadratic field K, the Dedekind zeta function is just $\zeta_K(s)=\zeta(s)L(s,\chi)$, and the residue is $L(1,\chi)$")

import Mathlib
import Definitions.Def_ClassNumberFormula_Kronecker
open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology Real

namespace ClassNumberFormula

theorem quadratic_dedekindZeta_eq_zeta_mul_L (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [NeZero (discr K).natAbs]
    (χ : DirichletCharacter ℂ (discr K).natAbs)
    (hχ : ∀ n : ℕ, χ n = (kroneckerSymbol (discr K) n : ℂ)) :
    (∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s) ∧
    Tendsto (fun s : ℝ => ((s : ℂ) - 1) * dedekindZeta K s) (𝓝[>] 1)
      (𝓝 (χ.LFunction 1)) := by sorry

end ClassNumberFormula
