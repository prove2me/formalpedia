-- Prove2me | Theorems.Thm_AutomorphicForm_IsArchTestFactor_exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det
-- name    : AutomorphicForm.IsArchTestFactor.exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/dd6cbabf-db16-5002-98cd-5fe331e86964
-- title:
--   Archimedean test factors descend to smooth functions on invertible matrices
-- statement:
--   Let $F$ be a field equipped with a number field structure, and let $fa$ be a complex-valued function on $\mathrm{GL}_2$ of the infinite adele ring of $F$. Assume $fa$ satisfies `IsArchTestFactor F fa`, i.e. two things: first, there is a function $\Phi$ on the space $\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to$ `mixedEmbedding.mixedSpace F` of $2\times 2$ arrays of entries in the mixed space of $F$ (the product of $\mathbb{R}$ over the real places and $\mathbb{C}$ over the complex places) which is $C^\infty$ as a function of real variables and satisfies $fa(g) = \Phi(\mathrm{archEntries}\,F\,g)$ for every $g$, where $\mathrm{archEntries}\,F\,g$ is the array obtained by transporting the matrix entries of $g$ through the ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace F`; and second, $fa$ has compact support. The conclusion is that such a $\Phi$ may be chosen with three further properties: $\Phi$ is $C^\infty$ over $\mathbb{R}$, $\Phi$ has compact support, the closed support of $\Phi$ is contained in the set of arrays $E$ whose determinant, formed after reading $E$ as a matrix via `Matrix.of`, is a unit of the mixed space, and still $fa(g) = \Phi(\mathrm{archEntries}\,F\,g)$ for all $g$.
--
--   This is support bookkeeping for the archimedean factors of factorizable test functions on $\mathrm{GL}_2$ over a number field: the smooth function on entry space representing such a factor can be taken compactly supported inside the invertible matrices, so that no mass sits on singular entry arrays. It is used in the construction of normalised archimedean test factors with prescribed size and in the comparison of test factors with twisted orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsArchTestFactor_exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det.lean

import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open scoped Classical in

theorem AutomorphicForm.IsArchTestFactor.exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det
    (F : Type) [Field F] [NumberField F] {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (hfa : IsArchTestFactor F fa) :
    ∃ Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
        tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} ∧ ∀ g, fa g = Φ (archEntries F g) := by sorry
