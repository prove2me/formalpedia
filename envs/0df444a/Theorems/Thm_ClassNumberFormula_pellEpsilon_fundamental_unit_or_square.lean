-- Prove2me | Theorems.Thm_ClassNumberFormula_pellEpsilon_fundamental_unit_or_square
-- name    : ClassNumberFormula.pellEpsilon_fundamental_unit_or_square
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T12:55:18.018677+00:00
-- url     : https://prove2.me/theorems/b0b3d264-d43e-4645-a675-6ad8b8df1dfe
-- title:
--   $\varepsilon=\frac12(t+u\sqrt d)$ is a fundamental unit of $\mathbb Q(\sqrt d)$ or the square of one
-- statement:
--   Let $d > 0$ be a fundamental discriminant and let $K = \mathbb Q(\sqrt d)$, presented as a quadratic number field $K$ with an element $\alpha$ satisfying $\alpha^2 = d$. Let $t>0$, $u>0$ be the solution of $t^2 - du^2 = 4$ with $u$ minimal and put $\varepsilon = \frac12(t + u\alpha)\in K$. Then there is a unit $\eta \in \mathcal O_K^\times$ such that
--
--   1. $\eta$ is a fundamental unit: every unit of $\mathcal O_K$ equals $\eta^n$ or $-\eta^n$ for some $n\in\mathbb Z$;
--   2. $\varepsilon = \eta$ or $\varepsilon = \eta^2$.
--
--   **Formalization Note** A fundamental unit is taken here to be any generator of the unit group modulo $\{\pm1\}$, without the normalisation $\eta > 1$ under a real embedding. The choice of square root $\alpha$ of $d$ replaces $\varepsilon$ by its conjugate $\varepsilon^{-1}$, and the statement holds for either choice.
-- source:
--   Wikipedia, "Class number formula" (revision oldid=1366411311), https://en.wikipedia.org/w/index.php?title=Class_number_formula&oldid=1366411311, section "Dirichlet class number formula" ("Then $\varepsilon$ is either a fundamental unit of the real quadratic field $\mathbb Q(\sqrt d)$ or the square of a fundamental unit.")

import Mathlib
import Definitions.Def_ClassNumberFormula_Kronecker
import Definitions.Def_ClassNumberFormula_FormClassNumber
open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology Real

namespace ClassNumberFormula

theorem pellEpsilon_fundamental_unit_or_square (d : ℤ) (hd : IsFundamentalDiscriminant d)
    (hpos : 0 < d) (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (α : K) (hα : α ^ 2 = (d : K)) :
    ∃ η : (𝓞 K)ˣ, (∀ v : (𝓞 K)ˣ, ∃ n : ℤ, v = η ^ n ∨ v = -η ^ n) ∧
      (((η : 𝓞 K) : K) = ((pellT d : K) + (pellU d : K) * α) / 2 ∨
        ((η : 𝓞 K) : K) ^ 2 = ((pellT d : K) + (pellU d : K) * α) / 2) := by sorry

end ClassNumberFormula
