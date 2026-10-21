-- Prove2me | Theorems.Thm_FiniteFields_LinearAlgebra_finiteRankFredholmDeterminant_swap
-- name    : FiniteFields.LinearAlgebra.finiteRankFredholmDeterminant_swap
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T01:59:17.566476+00:00
-- url     : https://prove2.me/theorems/30802288-3485-4230-ba0f-e98b8c98c7e5
-- title:
--   Sylvester's identity for Fredholm determinants: $\det(1 - X\,ba) = \det(1 - X\,ab)$
-- statement:
--   Let $R$ be a commutative ring and let $M$, $N$ be free $R$-modules of finite rank (the two ranks may differ). For an endomorphism $u$ of a free module of finite rank, write $\det(1 - Xu) \in R[X]$ for its Fredholm determinant, i.e. the reverse of the characteristic polynomial of $u$.
--
--   **Statement.** For all $R$-linear maps $a : M \to N$ and $b : N \to M$,
--   $$\det\nolimits_M\big(1 - X\,(b \circ a)\big) \;=\; \det\nolimits_N\big(1 - X\,(a \circ b)\big) \qquad \text{in } R[X].$$
--
--   This is the Sylvester (Weinstein–Aronszajn) determinant identity in Fredholm form: the Fredholm determinant of an operator that factors through a finite free module does not depend on the order of the two factors. It is the algebraic core of the finite-rank approximations of Dwork's completely continuous operator.
--
--   **Formalization Note.** In Lean, `finiteRankFredholmDeterminant a b` is by definition the Fredholm determinant of $b \circ a$ on $M$, so the statement reads `finiteRankFredholmDeterminant a b = finiteRankFredholmDeterminant b a`.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, §2–§3 (Fredholm determinants of the completely continuous operator $\psi \circ H$ and their finite-dimensional approximations). Auxiliary algebraic lemma in the formalization of §2–§3 of Dwork 1960; it has no direct counterpart in the paper. Lean: ported from the `finite_fields` project (commit e8b5bf14), file `WeilConjectures/LinearAlgebra/Fredholm.lean`, declaration `WeilConjectures.LinearAlgebra.finiteRankFredholmDeterminant_swap`

import Mathlib
import Definitions.Def_FiniteFields_Dwork_TraceFormula

open Module Polynomial PowerSeries
open FiniteFields.LinearAlgebra
universe u v w
variable {R : Type u} {M : Type v} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]

theorem FiniteFields.LinearAlgebra.finiteRankFredholmDeterminant_swap (a : M →ₗ[R] N) (b : N →ₗ[R] M) :
    finiteRankFredholmDeterminant a b = finiteRankFredholmDeterminant b a := by sorry
