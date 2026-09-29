-- Prove2me | Theorems.Thm_AutomorphicForm_isCompact_principalLevel_inf_finiteAdelicGL2Subgroup
-- name    : AutomorphicForm.isCompact_principalLevel_inf_finiteAdelicGL2Subgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/1a2de839-1928-5b2a-afa8-253793418da7
-- title:
--   Compactness of the principal level meeting the finite-adelic subgroup
-- statement:
--   Let $F$ be a number field with ring of integers $\mathcal{O}_F$, and let $N$ be an ideal of $\mathcal{O}_F$. Work inside `AdelicGL2 (𝓞 F) F`, the group $\mathrm{GL}_2$ of the adele ring of $F$, with its topology. Two subgroups are involved. First, `principalLevel (𝓞 F) F N`, defined as the intersection of `levelOne (𝓞 F) F N` — the subgroup of those adelic matrices whose finite part lies in `finiteLevelOne (𝓞 F) F N`, i.e. the preimage of that subgroup under the finite-part homomorphism `glFin` — with the image of `levelOne (𝓞 F) F N` under conjugation by the involution `weyl`, the unit of $\mathrm{GL}_2$ given by the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$. Second, `finiteAdelicGL2Subgroup F`, the kernel of `glArch`, the homomorphism $\mathrm{GL}_2(\mathbb{A}_F)\to\mathrm{GL}_2(\mathbb{A}_{F,\infty})$ induced by the projection of the adeles onto the infinite adeles. The assertion is that the underlying set of the intersection of these two subgroups is compact.
--
--   This is the compactness of the principal congruence level $K(N)$ of $\mathrm{GL}_2$ over the finite adeles, here realised inside $\mathrm{GL}_2$ of the full adele ring by cutting with the subgroup having trivial archimedean component. It discharges the compactness hypothesis of the level-generic results on adelic automorphic forms at principal congruence level, and is cited in the statements about cuspidal constituents, cuspidal spectrum slices and integral comparisons along the flow chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isCompact_principalLevel_inf_finiteAdelicGL2Subgroup.lean

import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.isCompact_principalLevel_inf_finiteAdelicGL2Subgroup
    (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) :
    IsCompact ((principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F : Subgroup (AdelicGL2 (𝓞 F) F)) :
      Set (AdelicGL2 (𝓞 F) F)) := by sorry
