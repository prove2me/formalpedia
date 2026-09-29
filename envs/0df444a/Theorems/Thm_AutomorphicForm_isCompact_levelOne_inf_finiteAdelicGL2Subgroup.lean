-- Prove2me | Theorems.Thm_AutomorphicForm_isCompact_levelOne_inf_finiteAdelicGL2Subgroup
-- name    : AutomorphicForm.isCompact_levelOne_inf_finiteAdelicGL2Subgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/a9be3cf9-647a-5c87-8c6a-2c1863f0b956
-- title:
--   Compactness of the level group with trivial archimedean part
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$, and let $N$ be an arbitrary ideal of $\mathcal{O}_F$ (no nonzeroness is assumed). Work inside $\mathrm{GL}_2$ of the adele ring of $F$, written `AdelicGL2 (𝓞 F) F`. Two subgroups are involved. First, `levelOne (𝓞 F) F N` is the preimage under the map $\mathrm{GL}_2(\mathbb{A}_F) \to \mathrm{GL}_2(\mathbb{A}_F^{\mathrm{f}})$ induced by the projection of the adeles to the finite adeles of the subgroup `finiteLevelOne (𝓞 F) F N`, whose elements are those $g \in \mathrm{GL}_2(\mathbb{A}_F^{\mathrm{f}})$ for which both the matrix of $g$ and the matrix of $g^{-1}$ satisfy the predicate `IsLevelOneMatrix (𝓞 F) F N`, the level-$N$ congruence condition at the finite places. Second, `finiteAdelicGL2Subgroup F` is the kernel of the map induced by the projection of the adeles to the infinite adeles, i.e. the elements whose archimedean component is the identity. The assertion is that the underlying set of the intersection of these two subgroups is a compact subset of $\mathrm{GL}_2(\mathbb{A}_F)$.
--
--   This is the compactness half of the standard fact that the level-$N$ group $K_1(N)$ is compact open in $\mathrm{GL}_2(\mathbb{A}_F^{\mathrm{f}})$, transported to the subgroup of $\mathrm{GL}_2(\mathbb{A}_F)$ with trivial archimedean component. It supplies the compactness hypothesis used by the results on level averages of convolutions, Hecke coset sums and reproducing test functions for cuspidal constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isCompact_levelOne_inf_finiteAdelicGL2Subgroup.lean

import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.isCompact_levelOne_inf_finiteAdelicGL2Subgroup
    (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) :
    IsCompact ((levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F : Subgroup (AdelicGL2 (𝓞 F) F)) :
      Set (AdelicGL2 (𝓞 F) F)) := by sorry
