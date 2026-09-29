-- Prove2me | Theorems.Thm_AutomorphicForm_IsFinTestFactor_exists_isCompact_isOpen_forall_mul_eq
-- name    : AutomorphicForm.IsFinTestFactor.exists_isCompact_isOpen_forall_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/9ed38ff4-efe7-5ff5-a25f-84b787368674
-- title:
--   Compact open right-invariance subgroup for finite test factors
-- statement:
--   Let $K$ be a field which is a number field, let $\mathbb{A}_K^{\mathrm{fin}}$ denote the finite adele ring of $\mathcal{O}_K$ in $K$, and let $ff : \mathrm{GL}_2(\mathbb{A}_K^{\mathrm{fin}}) \to \mathbb{C}$ be a function satisfying the predicate `IsFinTestFactor K ff`, that is: $ff$ is locally constant, and $ff$ has compact support in the sense that its topological support (the closure of the set where it is non-zero) is compact. The assertion is that there exists a subgroup $U$ of $\mathrm{GL}_2(\mathbb{A}_K^{\mathrm{fin}})$ whose underlying set is compact and open, such that for every $x \in \mathrm{GL}_2(\mathbb{A}_K^{\mathrm{fin}})$ and every $u \in U$ one has $ff(xu) = ff(x)$; thus $ff$ is invariant under right translation by a compact open subgroup. Note that $U$ is produced as a subgroup, not merely as a compact open subset, and that the invariance is asserted for all $x$ simultaneously.
--
--   This is the standard smoothness statement for test functions on a totally disconnected locally compact group: a locally constant, compactly supported function on $\mathrm{GL}_2$ of the finite adeles is right-invariant under some compact open subgroup, i.e. it is a smooth vector for the right regular action. It is used in the decomposition of factorizable test functions into sums of right convolutions and into sums of local factorizations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsFinTestFactor_exists_isCompact_isOpen_forall_mul_eq.lean

import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm IsDedekindDomain

theorem AutomorphicForm.IsFinTestFactor.exists_isCompact_isOpen_forall_mul_eq (K : Type) [Field K]
    [NumberField K] (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ) (hff : IsFinTestFactor K ff) :
    ∃ U : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)),
      IsCompact (U : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) ∧
        IsOpen (U : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) ∧
          ∀ x, ∀ u ∈ U, ff (x * u) = ff x := by sorry
