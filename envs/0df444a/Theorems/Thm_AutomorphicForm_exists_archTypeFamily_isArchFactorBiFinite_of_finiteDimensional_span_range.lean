-- Prove2me | Theorems.Thm_AutomorphicForm_exists_archTypeFamily_isArchFactorBiFinite_of_finiteDimensional_span_range
-- name    : AutomorphicForm.exists_archTypeFamily_isArchFactorBiFinite_of_finiteDimensional_span_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/d51ccfee-9d3b-5cef-8a1c-e21b31f27bb9
-- title:
--   Per-place finite translate spans yield a bi-finite archimedean type
-- statement:
--   Let $F$ be a field (no number-field hypothesis is imposed) and let $fa : \mathrm{GL}_2(\mathbb{A}_{F,\infty}) \to \mathbb{C}$ be a complex-valued function on $\mathrm{GL}_2$ of the infinite adele ring of $F$. Assume that for every infinite place $w$ of $F$ two finite-dimensionality conditions hold, where elements $k$ of the group `rowIsometrySubgroup₀ w.Completion` are transported into $\mathrm{GL}_2(\mathbb{A}_{F,\infty})$ by `archRowIsometryInclAt₀ F w`: the $\mathbb{C}$-span of the family of functions $x \mapsto fa(x \cdot k)$, indexed by $k$, is finite-dimensional, and so is the $\mathbb{C}$-span of the family $x \mapsto fa((x \cdot k)^{-1})$, that is, of the right translates by $k$ of the inversion composite $x \mapsto fa(x^{-1})$. The conclusion is the existence of a family `tys : ArchTypeFamily F` — for each infinite place $w$ a natural number, and indexed by it a finite list of data `ArchRepAt F w`, each consisting of a natural number $n$ together with a representation of `rowIsometrySubgroup₀ w.Completion` on $\mathbb{C}^n$ — such that `IsArchFactorBiFinite F tys fa` holds: the function $x \mapsto fa(x^{-1})$ lies in the infimum over the infinite places $w$ of the supremum over the listed representations at $w$ of the submodules `archFactorTypeSubmoduleAt F w`, and $fa$ itself lies in the corresponding infimum of suprema of the submodules `archFactorDualTypeSubmoduleAt F w`.
--
--   This is the expressiveness half of the bookkeeping that links bi-finiteness with respect to some family of archimedean types to purely quantitative finite-dimensionality of translate spans at each infinite place: abstract finiteness under the row-isometry group at every archimedean place is converted into membership in the archimedean type cut and in its dual cut for a suitable family. It is used in the construction of archimedean test factors with prescribed twisted orbital integrals, via [`AutomorphicForm.exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_forall_exists_contDiff_conjAe`](thm.html#AutomorphicForm.exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_forall_exists_contDiff_conjAe).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_archTypeFamily_isArchFactorBiFinite_of_finiteDimensional_span_range.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.exists_archTypeFamily_isArchFactorBiFinite_of_finiteDimensional_span_range
    (F : Type) [Field F] (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hfin : ∀ w : InfinitePlace F,
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
        fun x : GL (Fin 2) (InfiniteAdeleRing F) => fa (x * archRowIsometryInclAt₀ F w k))) ∧
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
        fun x : GL (Fin 2) (InfiniteAdeleRing F) => fa (x * archRowIsometryInclAt₀ F w k)⁻¹))) :
    ∃ tys : ArchTypeFamily F, IsArchFactorBiFinite F tys fa := by sorry
