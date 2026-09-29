-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_adelicMaximalCompact_finiteAdelic_coset_principalLevel
-- name    : AutomorphicForm.exists_finset_adelicMaximalCompact_finiteAdelic_coset_principalLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/33ccf308-9da2-5bbb-91e2-12e96adeeaae
-- title:
--   Finitely many principal-level cosets cover the finite maximal compact
-- statement:
--   Let $K$ be a number field and let $N$ be a nonzero ideal of $\mathcal O_K$. Work in $\mathrm{GL}_2$ of the adele ring of $K$. Two subgroups are involved: `adelicMaximalCompact K`, consisting of those $k$ whose finite-adelic component lies in $\mathrm{GL}_2(\widehat{\mathcal O}_K)$ (level zero at the unit ideal) and whose component at each infinite place $w$ is a row isometry, i.e. has determinant of absolute value $1$ and preserves the form $\lVert x\rVert^2+\lVert y\rVert^2$ under $(x,y)\mapsto(x,y)k$; and `finiteAdelicGL2Subgroup K`, the kernel of the projection to $\mathrm{GL}_2$ of the infinite adeles. The assertion is that there exist $n\in\mathbb N$ and $r\colon \mathrm{Fin}\,n\to\mathrm{GL}_2(\mathbb A_K)$ with each $r_i$ lying in both of these subgroups, such that every $k$ lying in both subgroups satisfies $r_i^{-1}k\in \big(\mathrm{principalLevel}\,\mathcal O_K\,K\,N\big)\cap\mathrm{finiteAdelicGL2Subgroup}\,K$ for some $i$, where `principalLevel` is the intersection of the level-$N$ subgroup `levelOne` with its conjugate by the Weyl element $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   This is the statement that the principal congruence subgroup of level $N$ has finite index in the finite part of the standard maximal compact subgroup of $\mathrm{GL}_2(\mathbb A_K)$, recorded with explicit coset representatives in $\mathrm{GL}_2(\mathbb A_K)$ rather than as a statement about a quotient. It feeds the finite-dimensionality of level-type orbit spaces used in the theory of adelic automorphic forms, via [`AutomorphicForm.exists_finiteDimensional_biInvariant_levelTypeOrbitSubmodule_maximalCompact_detOne`](thm.html#AutomorphicForm.exists_finiteDimensional_biInvariant_levelTypeOrbitSubmodule_maximalCompact_detOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_adelicMaximalCompact_finiteAdelic_coset_principalLevel.lean

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm

theorem AutomorphicForm.exists_finset_adelicMaximalCompact_finiteAdelic_coset_principalLevel
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) :
    ∃ (n : ℕ) (r : Fin n → AdelicGL2 (𝓞 K) K),
      (∀ i, r i ∈ adelicMaximalCompact K ∧ r i ∈ finiteAdelicGL2Subgroup K) ∧
      ∀ k ∈ adelicMaximalCompact K, k ∈ finiteAdelicGL2Subgroup K →
        ∃ i, (r i)⁻¹ * k ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K := by sorry
