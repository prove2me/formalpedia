-- Prove2me | Theorems.Thm_AutomorphicForm_exists_maximalCompactAway_subset_of_mem_nhds_one
-- name    : AutomorphicForm.exists_maximalCompactAway_subset_of_mem_nhds_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/d289e73f-53b4-56c6-b0ff-9153d77aa225
-- title:
--   The subgroups K^S shrink to 1 in GL₂(mathbb A_F)
-- statement:
--   Let $F$ be a number field and let $W$ be a subset of $\mathrm{GL}_2(\mathbb A_F)$, the group `AdelicGL2 (𝓞 F) F` of invertible $2\times 2$ matrices over the adele ring of $F$, which is assumed to be a neighbourhood of the identity element. The assertion is that there exists a finite set $S_0$ of nonzero primes of $\mathcal O_F$ (elements of `HeightOneSpectrum (𝓞 F)`) such that the underlying set of the subgroup `maximalCompactAway F S₀` is contained in $W$. By definition `maximalCompactAway F S₀` is the intersection of three subgroups of $\mathrm{GL}_2(\mathbb A_F)$: `adelicMaximalCompact F`, consisting of those $k$ whose finite-adelic image under `glFin` lies in `finiteIntegralGL2 (𝓞 F) F` and whose archimedean component at every infinite place $w$ of $F$ satisfies `IsRowIsometry`; the kernel of the archimedean projection `glArch`, i.e. the elements with trivial component in $\mathrm{GL}_2(\mathbb A_{F,\infty})$; and, for each $v \in S_0$, the kernel of the map sending $k$ to the image of its finite part under `finComponent (𝓞 F) F v`, i.e. the elements whose component in $\mathrm{GL}_2(F_v)$ is trivial.
--
--   This is the statement that the compact subgroups $\mathbf K^{S}$ — integral at all finite places, trivial at the archimedean places and at the places of $S$ — form a family shrinking to the identity, so that they give a neighbourhood basis at $1$ up to cofinality in $S$. It is used to attach a finite level to a smooth vector: an automorphic form invariant under a neighbourhood of $1$ is invariant under some $\mathbf K^{S_0}$, as in the results on forms that agree away from a finite set of places and in the associated integral estimates that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_maximalCompactAway_subset_of_mem_nhds_one.lean

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm Filter Topology

theorem AutomorphicForm.exists_maximalCompactAway_subset_of_mem_nhds_one
    (F : Type) [Field F] [NumberField F]
    (W : Set (AdelicGL2 (𝓞 F) F)) (_hW : W ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F)) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)),
      (maximalCompactAway F S₀ : Set (AdelicGL2 (𝓞 F) F)) ⊆ W := by sorry
