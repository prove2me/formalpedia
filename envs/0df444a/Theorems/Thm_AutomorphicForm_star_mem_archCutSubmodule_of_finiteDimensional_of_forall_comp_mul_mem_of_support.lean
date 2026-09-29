-- Prove2me | Theorems.Thm_AutomorphicForm_star_mem_archCutSubmodule_of_finiteDimensional_of_forall_comp_mul_mem_of_support
-- name    : AutomorphicForm.star_mem_archCutSubmodule_of_finiteDimensional_of_forall_comp_mul_mem_of_support
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/9de9f6b4-5049-5eff-b5cd-f8bf3c096c10
-- title:
--   Conjugate-inverse involution preserves the archimedean type cut
-- statement:
--   Let $F$ be a number field and let $\mathrm{tys}$ be an archimedean type family for $F$: data consisting of a cardinality $\mathrm{tys.card}(w) \in \mathbb{N}$ for each infinite place $w$ of $F$ together with, for each $w$ and each $i < \mathrm{tys.card}(w)$, an archimedean type $\mathrm{tys.rep}\,w\,i$ at $w$, that is a natural number $n$ and a representation $\rho$ of the group `rowIsometrySubgroup₀ w.Completion` on $\mathbb{C}^n$. Let $S$ be a subgroup of $G = \mathrm{GL}_2$ of the adele ring of $F$ containing the image under `rowIsometryInclAt₀ F w` of every element of `rowIsometrySubgroup₀ w.Completion`, for every infinite place $w$. Let $E$ be a finite-dimensional $\mathbb{C}$-subspace of the functions $G \to \mathbb{C}$ such that: $E$ is stable under right translation by every $s \in S$, i.e. $x \mapsto v(xs) \in E$ for $v \in E$; every $v \in E$ vanishes off $S$; for every $v \in E$, every infinite place $w$ and every $x \in G$ the orbit map $k \mapsto v(x \cdot \mathrm{rowIsometryInclAt₀}\,F\,w\,k)$ is continuous on `rowIsometrySubgroup₀ w.Completion`; and $E$ lies in the archimedean cut $\bigsqcap_{w \mid \infty} \bigsqcup_{i < \mathrm{tys.card}(w)} \mathrm{typeSubmodule}(\mathrm{rowIsometryInclAt₀}\,F\,w, (\mathrm{tys.rep}\,w\,i).\rho)$ of $\mathrm{tys}$. Then for every $v \in E$ the function $x \mapsto \overline{v(x^{-1})}$ again lies in the archimedean cut of the same family $\mathrm{tys}$.
--
--   This is the $*$-stability statement for archimedean types: the involution $v^*(x) = \overline{v(x^{-1})}$ does not leave the archimedean type cut, on a finite-dimensional space of functions that is right $S$-stable, supported in $S$ and continuous along the orbits of the determinant-one row-isometry groups at the infinite places. It is used in the construction of the finite-dimensional bi-invariant level–type orbit submodule for the maximal compact subgroup, where $S$ is the relevant compact group and $E$ the orbit space; the proof invokes the statement that matrix coefficients of a finite-dimensional right-translation-stable space lie in the corresponding sup of type submodules, and their inverse matrix coefficients in the sup for the dual representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_star_mem_archCutSubmodule_of_finiteDimensional_of_forall_comp_mul_mem_of_support.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped ComplexConjugate
open NumberField AutomorphicForm

theorem AutomorphicForm.star_mem_archCutSubmodule_of_finiteDimensional_of_forall_comp_mul_mem_of_support
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (S : Subgroup (AdelicGL2 (𝓞 F) F))
    (hS : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), rowIsometryInclAt₀ F w k ∈ S)
    (E : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hEfd : FiniteDimensional ℂ E)
    (hER : ∀ s ∈ S, ∀ v ∈ E, (fun x => v (x * s)) ∈ E)
    (hsupp : ∀ v ∈ E, ∀ x : AdelicGL2 (𝓞 F) F, v x ≠ 0 → x ∈ S)
    (hcont : ∀ v ∈ E, ∀ (w : InfinitePlace F) (x : AdelicGL2 (𝓞 F) F),
      Continuous fun k : rowIsometrySubgroup₀ w.Completion => v (x * rowIsometryInclAt₀ F w k))
    (hEt : E ≤ archCutSubmodule F tys) :
    ∀ v ∈ E, (fun x => conj (v x⁻¹)) ∈ archCutSubmodule F tys := by sorry
