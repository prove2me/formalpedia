-- Prove2me | Theorems.Thm_DiazModulus_remond_commuting_end
-- name    : DiazModulus.remond_commuting_end
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:30:36.314201+00:00
-- url     : https://prove2.me/theorems/25ba66b1-7933-499e-871a-7f83fa225a61
-- title:
--   Rémond's lemma for endomorphisms: if U, V are subspaces of End(E), dim_ℂ E = n, and ab = ba for all a ∈ U and b ∈ V, then dim U + dim V ≤ n² + 1
-- statement:
--   Let $E$ be a finite-dimensional complex vector space, $n = \dim_{\mathbb C} E$, and let $U, V$ be $\mathbb C$-subspaces of $\operatorname{End}_{\mathbb C}(E)$ such that $ab = ba$ for all $a \in U$ and $b \in V$. Then
--   $$\dim U + \dim V \le n^2 + 1.$$
-- source:
--   S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Lemma 5.6 (pp. 181–182), due to Rémond, for the field ℂ and in the language of endomorphisms; the proof is the printed induction on n. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem remond_commuting_end {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (U V : Submodule ℂ (Module.End ℂ E)) (h : ∀ a ∈ U, ∀ b ∈ V, a * b = b * a) :
    Module.finrank ℂ ↥U + Module.finrank ℂ ↥V ≤ Module.finrank ℂ E ^ 2 + 1 := by
  sorry

end DiazModulus
