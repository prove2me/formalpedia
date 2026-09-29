-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isHeckeCosetSystem_levelOne_and_principalLevel_heckeGen_of_not_dvd
-- name    : AutomorphicForm.exists_isHeckeCosetSystem_levelOne_and_principalLevel_heckeGen_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/a2ae73ba-805f-56ff-900e-111a24167ad4
-- title:
--   A common coset system for U₁(N) and K(N) at v ∤ N
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal{O}_K$, let $N$ be an ideal of $\mathcal{O}_K$, and let $v$ be a nonzero prime of $\mathcal{O}_K$ (a point of the height-one spectrum) with $v \nmid N$. Write $t_v :=$ `heckeGen` $(\mathcal{O}_K, K, v)$ for the element of $\mathrm{GL}_2(\mathbb{A}_K)$ obtained by applying `heckeGenAt` to the distinguished uniformizer unit of $K_v$, that is the diagonal matrix $\mathrm{diag}(u,1)$ whose entry $u$ is the adele that is a uniformizer at $v$ and $1$ at all other places. Let $U_1 :=$ `levelOne` $(\mathcal{O}_K, K, N) \sqcap$ `finiteAdelicGL2Subgroup` $K$, the subgroup of those $g \in \mathrm{GL}_2(\mathbb{A}_K)$ with trivial archimedean component (i.e. lying in the kernel of `glArch`) whose finite part, and the finite part of whose inverse, both satisfy the predicate `IsLevelOneMatrix` at level $N$; and let $U_0 :=$ `principalLevel` $(\mathcal{O}_K, K, N) \sqcap$ `finiteAdelicGL2Subgroup` $K$, where `principalLevel` is the intersection of `levelOne` with its conjugate by the antidiagonal involution $\begin{pmatrix}0&1\\1&0\end{pmatrix}$. The assertion is that there exists a single family $(x_i)_{i \in \mathrm{Fin}(N(v)+1)}$ of elements of $\mathrm{GL}_2(\mathbb{A}_K)$, where $N(v)$ is the absolute norm of $v$, which is an `IsHeckeCosetSystem` for $t_v$ simultaneously with respect to $U_1$ and with respect to $U_0$: for each of the two groups $U$, every $x_i$ lies in the double coset $U t_v U$, every element of $U t_v U$ has the same image in $\mathrm{GL}_2(\mathbb{A}_K)/U$ as some $x_i$, and $i \mapsto x_i U$ is injective.
--
--   This is the classical decomposition of the Hecke double coset at a prime $v$ not dividing the level into exactly $N(v)+1$ left cosets, in the adelic $\mathrm{GL}_2$ setting, with the additional point that one family of representatives works for the level-one group and for the principal congruence group at the same time. It is obtained from the local statement [`HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen`](thm.html#HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen), and it feeds the comparison of Hecke coset sums with isotypic cuspidal submodules at principal level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isHeckeCosetSystem_levelOne_and_principalLevel_heckeGen_of_not_dvd.lean

import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_LocalLanglands_HeckeCosetSystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain HeckeIntegralSeam

theorem AutomorphicForm.exists_isHeckeCosetSystem_levelOne_and_principalLevel_heckeGen_of_not_dvd
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ v.asIdeal ∣ N) :
    ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AutomorphicForm.AdelicGL2 (𝓞 K) K,
      IsHeckeCosetSystem (levelOne (𝓞 K) K N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K)
          (heckeGen (𝓞 K) K v) reps ∧
        IsHeckeCosetSystem (principalLevel (𝓞 K) K N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K)
          (heckeGen (𝓞 K) K v) reps := by sorry
