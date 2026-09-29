-- Prove2me | Theorems.Thm_AutomorphicForm_exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet
-- name    : AutomorphicForm.exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/0396caeb-7e94-50c1-a9c3-6ab00a6a1814
-- title:
--   Splitting an adelic GL₂ element along the good places
-- statement:
--   Let $K$ be a number field, $N$ an ideal of $\mathcal{O}_K$ and $S$ a finite set of height-one primes of $\mathcal{O}_K$ such that every $v$ with $v.\mathrm{asIdeal} \mid N$ lies in $S$. Let $z$ be an element of `AdelicGL2 (𝓞 K) K`, the general linear group of degree $2$ over the adele ring of $K$, and assume that for every prime $v \notin S$ the component at $v$ of the finite part $\mathrm{glFin}(z)$ of $z$ lies in `localIntegralSet K v`, that is, both that matrix and its inverse lie in `integralMatrixSet` of the valuation ring $\mathcal{O}_v \subseteq K_v$ of the $v$-adic completion. Then there exist $z_1, z_2 \in \mathrm{GL}_2(\mathbb{A}_K)$ with $z = z_1 z_2$ such that: (i) $z_2$ lies in the intersection of `levelOne (𝓞 K) K N`, i.e. the finite part of $z_2$ and its inverse both satisfy the predicate `IsLevelOneMatrix` for $N$, with `finiteAdelicGL2Subgroup K`, the kernel of the archimedean projection $\mathrm{glArch}$, so that the archimedean component of $z_2$ is trivial; and (ii) for every $v \notin S$ and every $x_v \in \mathrm{GL}_2(K_v)$, the element $z_1$ commutes with the image of $x_v$ under the single-place embedding [`UnramifiedWhittaker.placeEmbed K v`](def/UnramifiedWhittaker_HeckeRecursion.html#L47) of $\mathrm{GL}_2(K_v)$ into $\mathrm{GL}_2(\mathbb{A}_K)$.
--
--   This is the standard adelic bookkeeping step that cuts an adelic matrix along the idempotent of a finite set of places: the components outside $S$, being integral, can be absorbed into the level group at level $N$, leaving a factor supported at $S$ and at the archimedean places, hence commuting with everything coming from the places outside $S$. It is used in the analysis of right convolution by unit-factorizable bi-invariant test functions, in [`AutomorphicForm.exists_isUnitFactorizableAboveOfType_biInvariant_rightConv_ne_zero_of_mem_archCutSubmodule`](thm.html#AutomorphicForm.exists_isUnitFactorizableAboveOfType_biInvariant_rightConv_ne_zero_of_mem_archCutSubmodule).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (z : AdelicGL2 (𝓞 K) K)
    (hz : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v) :
    ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K, z = z₁ * z₂ ∧
      z₂ ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
        z₁ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * z₁ := by sorry
