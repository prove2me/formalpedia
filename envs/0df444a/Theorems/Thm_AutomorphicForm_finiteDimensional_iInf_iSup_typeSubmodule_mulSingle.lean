-- Prove2me | Theorems.Thm_AutomorphicForm_finiteDimensional_iInf_iSup_typeSubmodule_mulSingle
-- name    : AutomorphicForm.finiteDimensional_iInf_iSup_typeSubmodule_mulSingle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/3f174aa2-86bd-51e5-965f-3a430b3ac1e1
-- title:
--   Finite-dimensionality of the multi-place isotypic intersection
-- statement:
--   Let $Pl$ be a finite type, and for each $w \in Pl$ let $K_w$ be a group; write $G = \prod_{w} K_w$ for the product group and, for each $w$, let $\mathrm{mulSingle}_w \colon K_w \to G$ be the monoid homomorphism placing an element in the $w$-th coordinate and $1$ elsewhere. For each $w$ let $\iota_w$ be a finite type and, for each $i \in \iota_w$, let $W_{w,i}$ be a finite-dimensional complex vector space equipped with a representation $\rho_{w,i}$ of $K_w$. For a representation $\rho$ of a group $H$ on $W$ and a homomorphism $j \colon H \to G$, [`AutomorphicForm.typeSubmodule`](def/AutomorphicForm_IsotypicCuspSpace.html#L471) is the $\mathbb{C}$-submodule of $G \to \mathbb{C}$ spanned by all functions lying in the range of some $\mathbb{C}$-linear map $T \colon W \to (G \to \mathbb{C})$ that is right equivariant, i.e. satisfies $T(\rho(k)v)(x) = (Tv)(x\, j(k))$ for all $k \in H$, $v \in W$, $x \in G$. The assertion is that the submodule
--   $$\bigcap_{w \in Pl} \ \sum_{i \in \iota_w} \ \mathrm{typeSubmodule}(\mathrm{mulSingle}_w, \rho_{w,i})$$
--   of $G \to \mathbb{C}$, where the sum is the supremum of submodules, is finite-dimensional over $\mathbb{C}$. No topology or continuity hypothesis is imposed on the groups $K_w$ or on the functions.
--
--   This is the abstract finiteness statement underlying the finite-dimensionality of spaces of automorphic forms of prescribed type at each of finitely many places: a function on a finite product of groups that is of finite type, in the sense of spanning the image of finitely many equivariant maps, in each factor separately lies in a finite-dimensional space of matrix-coefficient-like functions. It is used by [`AutomorphicForm.exists_finiteDimensional_biInvariant_levelTypeOrbitSubmodule_maximalCompact_detOne`](thm.html#AutomorphicForm.exists_finiteDimensional_biInvariant_levelTypeOrbitSubmodule_maximalCompact_detOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_finiteDimensional_iInf_iSup_typeSubmodule_mulSingle.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.finiteDimensional_iInf_iSup_typeSubmodule_mulSingle
    {Pl : Type*} [Fintype Pl] [DecidableEq Pl] {K : Pl → Type*} [∀ w, Group (K w)]
    {ι : Pl → Type*} [∀ w, Fintype (ι w)]
    {W : ∀ w, ι w → Type*} [∀ w i, AddCommGroup (W w i)] [∀ w i, Module ℂ (W w i)]
    [∀ w i, FiniteDimensional ℂ (W w i)]
    (ρ : ∀ w i, Representation ℂ (K w) (W w i)) :
    FiniteDimensional ℂ
      ↥(⨅ w, ⨆ i, AutomorphicForm.typeSubmodule (MonoidHom.mulSingle K w) (ρ w i)) := by sorry
