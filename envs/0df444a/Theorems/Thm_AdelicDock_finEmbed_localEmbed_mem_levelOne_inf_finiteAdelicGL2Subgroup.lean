-- Prove2me | Theorems.Thm_AdelicDock_finEmbed_localEmbed_mem_levelOne_inf_finiteAdelicGL2Subgroup
-- name    : AdelicDock.finEmbed_localEmbed_mem_levelOne_inf_finiteAdelicGL2Subgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/1dab2384-6f2c-5e46-8040-78ed2bb74c44
-- title:
--   Integral matrix at a place prime to the level lies in U₁(N)
-- statement:
--   Let $F$ be a number field with ring of integers $\mathcal{O}_F$, let $v$ be a nonzero prime of $\mathcal{O}_F$ (a point of the height one spectrum), with completion $F_v =$ `v.adicCompletion F` and valuation ring $\mathcal{O}_v =$ `v.adicCompletionIntegers F`, and let $N$ be an ideal of $\mathcal{O}_F$ such that the prime $v$ does not divide $N$. Let $k \in \mathrm{GL}_2(F_v)$ lie in `integralSubgroup`, that is, in the range of the homomorphism $\mathrm{GL}_2(\mathcal{O}_v) \to \mathrm{GL}_2(F_v)$ induced entrywise by the structure map $\mathcal{O}_v \to F_v$. Form the element of $\mathrm{GL}_2$ of the full adele ring obtained by first applying `localEmbed`, which sends $k$ to the finite-adelic matrix whose entries are the entries of the identity matrix with their $v$-components replaced by the corresponding entries of $k$, and then `finEmbed`, which pairs a finite-adelic matrix with the identity matrix over the infinite adeles. The assertion is that this element lies in the intersection of two subgroups of $\mathrm{GL}_2(\mathbb{A}_F)$: `levelOne (𝓞 F) F N`, the preimage under the finite-part homomorphism `glFin` of the subgroup `finiteLevelOne` of those $g$ for which both $g$ and $g^{-1}$ satisfy the level-$N$ entry condition `IsLevelOneMatrix (𝓞 F) F N`; and `finiteAdelicGL2Subgroup F`, the kernel of the archimedean-part homomorphism `glArch`, i.e. the matrices with trivial archimedean component.
--
--   This records that $\mathrm{GL}_2(\mathcal{O}_v)$, placed at a single finite place $v$ prime to the level and with the identity at all other places, sits inside the adelic level group $U_1(N)$ and has trivial component at infinity. It is used when local integral Hecke data at $v$ are transported to the adelic automorphic setting, for instance in the construction of Hecke coset systems and in the results on level structures for cuspidal Hecke eigenforms that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdelicDock_finEmbed_localEmbed_mem_levelOne_inf_finiteAdelicGL2Subgroup.lean

import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_LocalLanglands_LocalHeckeInstance

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm LocalGL2 NumberField.AdelicLevel

theorem AdelicDock.finEmbed_localEmbed_mem_levelOne_inf_finiteAdelicGL2Subgroup
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : k ∈ integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F)) :
    finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v k) ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by sorry
