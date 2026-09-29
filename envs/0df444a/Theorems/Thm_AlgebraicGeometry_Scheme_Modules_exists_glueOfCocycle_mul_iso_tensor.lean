-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_glueOfCocycle_mul_iso_tensor
-- name    : AlgebraicGeometry.Scheme.Modules.exists_glueOfCocycle_mul_iso_tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/fbcafa7f-0066-597e-bf3f-e5a14cf20a44
-- title:
--   Product of unit cocycles glues to the tensor product
-- statement:
--   Let $X$ be a scheme, let $\iota$ be a type and let $U : \iota \to X.\mathrm{Opens}$ be a family of open subsets with $\bigsqcup_i U_i = \top$, so that the $U_i$ cover $X$. Let $c$ and $c'$ be two elements of `Scheme.Modules.UnitCocycle U`, that is, families of sections $u_{ij} \in \Gamma(X, U_i \sqcap U_j)$ with $u_{ii} = 1$ and with $u_{ij}|_{U_i \sqcap U_j \sqcap U_k} \cdot u_{jk}|_{U_i \sqcap U_j \sqcap U_k} = u_{ik}|_{U_i \sqcap U_j \sqcap U_k}$ for all $i,j,k$. Write $c \cdot c'$ for the cocycle `c.mul c'` with entries $u_{ij} u'_{ij}$, and for a cocycle $d$ write $\mathrm{glueOfCocycle}\,d$ for the sheaf of modules on $X$ whose sections over an open $T$ are the families $(x_i)_{i}$, $x_i \in \Gamma(X, T \sqcap U_i)$, satisfying $x_i = d_{ij} x_j$ after restriction to $T \sqcap U_i \sqcap U_j$, and $\mathrm{glueFrame}\,d\,i \in \Gamma(\mathrm{glueOfCocycle}\,d, U_i)$ for the section given by the family $k \mapsto d_{ki}$ (transported along $U_i \sqcap U_k = U_k \sqcap U_i$). The assertion is that there is an isomorphism $\varphi$ of sheaves of modules on $X$ from $\mathrm{glueOfCocycle}(c \cdot c')$ to the monoidal tensor product $\mathrm{glueOfCocycle}\,c \otimes \mathrm{glueOfCocycle}\,c'$ such that for every $i$ the map $\varphi$ on sections over $U_i$ carries $\mathrm{glueFrame}(c\cdot c')\,i$ to $\mathrm{tensorSections}$ of $\mathrm{glueFrame}\,c\,i$ and $\mathrm{glueFrame}\,c'\,i$, the canonical image of the elementary tensor of the two frames in the sections of the tensor product.
--
--   This is the multiplicativity of the passage from a Čech $1$-cocycle with values in $\mathcal{O}_X^\times$ to the associated invertible sheaf, in the normalised form that records the effect on the distinguished local frames. It is used in the construction of the invertible sheaf attached to a norm, in [`AlgebraicGeometry.Scheme.Modules.exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_glueOfCocycle_mul_iso_tensor.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace MonoidalCategory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_glueOfCocycle_mul_iso_tensor
    {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤) (c c' : Scheme.Modules.UnitCocycle U) :
    ∃ φ : Scheme.Modules.glueOfCocycle (c.mul c') ≅ Scheme.Modules.glueOfCocycle c ⊗ Scheme.Modules.glueOfCocycle c',
      ∀ i, φ.hom.app (U i) (Scheme.Modules.glueFrame (c.mul c') i) =
        Scheme.Modules.tensorSections (Scheme.Modules.glueFrame c i) (Scheme.Modules.glueFrame c' i) := by sorry
