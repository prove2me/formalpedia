-- Prove2me | Theorems.Thm_AutomorphicForm_matrixCoeff_mem_iSup_typeSubmodule_and_matrixCoeff_inv_mem_iSup_typeSubmodule_dual_of_forall_mem_iSup_typeSubmodule_comp
-- name    : AutomorphicForm.matrixCoeff_mem_iSup_typeSubmodule_and_matrixCoeff_inv_mem_iSup_typeSubmodule_dual_of_forall_mem_iSup_typeSubmodule_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/495bdf0e-f4a5-51aa-a527-629b5581b6f0
-- title:
--   Types of matrix coefficients of a right-translation-stable space
-- statement:
--   Let $G$, $K_c$ and $H$ be groups, $\iota\colon K_c\to G$ and $j\colon H\to K_c$ group homomorphisms with $j$ injective, and let $E$ be a complex subspace of the space of functions $G\to\mathbb{C}$ which is finite-dimensional over $\mathbb{C}$ and stable under right translation through $\iota$, i.e. for every $\kappa\in K_c$ and every $v\in E$ the function $x\mapsto v(x\,\iota(\kappa))$ again lies in $E$. Let $(W_i)_{i\in J}$ be a family of complex vector spaces with representations $\rho_i$ of $H$ on $W_i$, and assume every $v\in E$ lies in the supremum over $i$ of the submodules [`AutomorphicForm.typeSubmodule (ι.comp j) (ρ i)`](def/AutomorphicForm_IsotypicCuspSpace.html#L471), that is, in the sum of the $\mathbb{C}$-spans of the ranges of those linear maps $T\colon W_i\to(G\to\mathbb{C})$ satisfying $T(\rho_i(k)w)(x)=T(w)(x\,\iota(j(k)))$ for all $k\in H$, $w\in W_i$, $x\in G$. Then for every $\mathbb{C}$-linear functional $\lambda$ on $E$ and every $v\in E$: the function $K_c\to\mathbb{C}$, $\kappa\mapsto\lambda\bigl(x\mapsto v(x\,\iota(\kappa))\bigr)$, lies in the supremum over $i$ of [`AutomorphicForm.typeSubmodule j (ρ i)`](def/AutomorphicForm_IsotypicCuspSpace.html#L471) (the analogous spans of ranges of maps $W_i\to(K_c\to\mathbb{C})$ equivariant for right translation through $j$), and the function $\kappa\mapsto\lambda\bigl(x\mapsto v(x\,\iota(\kappa^{-1}))\bigr)$ lies in the supremum over $i$ of [`AutomorphicForm.typeSubmodule j (ρ i).dual`](def/AutomorphicForm_IsotypicCuspSpace.html#L471), formed from the contragredient representations of $H$ on the dual spaces of the $W_i$.
--
--   This is the algebraic bookkeeping of the $H$-types of matrix coefficients: for the representation of $K_c$ on $E$ by right translation through $\iota$, the coefficients $\kappa\mapsto\lambda(\kappa\cdot v)$ carry the same types $(\rho_i)$ as the vectors of $E$, while the coefficients of $\kappa^{-1}$ carry the contragredient types. It is used to transfer type hypotheses on a finite-dimensional translation-stable space of functions to the entries of the translation matrices, in the results [`AutomorphicForm.star_mem_archCutSubmodule_and_star_mem_archDualCutSubmodule_of_continuous`](thm.html#AutomorphicForm.star_mem_archCutSubmodule_and_star_mem_archDualCutSubmodule_of_continuous) and [`AutomorphicForm.star_mem_archCutSubmodule_of_finiteDimensional_of_forall_comp_mul_mem_of_support`](thm.html#AutomorphicForm.star_mem_archCutSubmodule_of_finiteDimensional_of_forall_comp_mul_mem_of_support).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_matrixCoeff_mem_iSup_typeSubmodule_and_matrixCoeff_inv_mem_iSup_typeSubmodule_dual_of_forall_mem_iSup_typeSubmodule_comp.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.matrixCoeff_mem_iSup_typeSubmodule_and_matrixCoeff_inv_mem_iSup_typeSubmodule_dual_of_forall_mem_iSup_typeSubmodule_comp
    {G Kc H : Type*} [Group G] [Group Kc] [Group H] (ι : Kc →* G) (j : H →* Kc)
    (hj : Function.Injective j) (E : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ E]
    (hE : ∀ κ : Kc, ∀ v ∈ E, (fun x => v (x * ι κ)) ∈ E)
    {J : Type*} {W : J → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ H (W i))
    (hEρ : ∀ v ∈ E, v ∈ ⨆ i, AutomorphicForm.typeSubmodule (ι.comp j) (ρ i))
    (lam : Module.Dual ℂ E) (v : E) :
    (fun κ : Kc => lam ⟨fun x => (v : G → ℂ) (x * ι κ), hE κ v v.2⟩) ∈
        ⨆ i, AutomorphicForm.typeSubmodule j (ρ i) ∧
      (fun κ : Kc => lam ⟨fun x => (v : G → ℂ) (x * ι κ⁻¹), hE κ⁻¹ v v.2⟩) ∈
        ⨆ i, AutomorphicForm.typeSubmodule j (ρ i).dual := by sorry
