-- Prove2me | Theorems.Thm_AutomorphicForm_typeSubmodule_inf_typeSubmodule_eq_bot
-- name    : AutomorphicForm.typeSubmodule_inf_typeSubmodule_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/b6299125-4b34-5e7a-a43c-c7d7e5cb79db
-- title:
--   Type pieces of inequivalent irreducibles meet in zero
-- statement:
--   Let $H$ and $G$ be groups, $\iota \colon H \to G$ a group homomorphism, and let $\rho$ and $\rho'$ be representations of $H$ over $\mathbb{C}$ on complex vector spaces $W$ and $W'$ respectively, each assumed irreducible (instances `Representation.IsIrreducible`); no finite-dimensionality is assumed. Suppose moreover that the type $\rho.\mathrm{Equiv}\ \rho'$ of isomorphisms of representations between $\rho$ and $\rho'$ is empty. For a representation $\sigma$ of $H$ on a space $V$, the submodule `typeSubmodule ι σ` of the $\mathbb{C}$-vector space $G \to \mathbb{C}$ of all complex-valued functions on $G$ is defined to be the $\mathbb{C}$-linear span of the set of functions lying in the range of some $\mathbb{C}$-linear map $T \colon V \to (G \to \mathbb{C})$ satisfying the right-equivariance condition `IsRightEquivariant ι σ T`, namely $T(\sigma(k)v)(x) = T(v)(x\,\iota(k))$ for all $k \in H$, $v \in V$ and $x \in G$. The conclusion is that the infimum of the two submodules $\mathtt{typeSubmodule}\ \iota\ \rho$ and $\mathtt{typeSubmodule}\ \iota\ \rho'$ of $G \to \mathbb{C}$ is the zero submodule; that is, the only function on $G$ lying in both type pieces is $0$.
--
--   This is the isotypic form of Schur's lemma for the type pieces of functions on a group: pieces attached to inequivalent irreducible representations of $H$ are disjoint inside $G \to \mathbb{C}$. It is used in the analysis of cuspidal constituents, where it separates the contributions of distinct local types in the results on level-invariant and archimedean-cut subspaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_typeSubmodule_inf_typeSubmodule_eq_bot.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.typeSubmodule_inf_typeSubmodule_eq_bot
    {H G : Type*} [Group H] [Group G]
    {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ι : H →* G) (ρ : Representation ℂ H W) (ρ' : Representation ℂ H W')
    [ρ.IsIrreducible] [ρ'.IsIrreducible] (hne : IsEmpty (ρ.Equiv ρ')) :
    typeSubmodule ι ρ ⊓ typeSubmodule ι ρ' = ⊥ := by sorry
