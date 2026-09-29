-- Prove2me | Theorems.Thm_AutomorphicForm_norm_archChar_eq_one_of_mem_archCutSubmodule_ofChar
-- name    : AutomorphicForm.norm_archChar_eq_one_of_mem_archCutSubmodule_ofChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/d10d920c-fc6b-5244-b1da-a3a109780c0a
-- title:
--   Archimedean type characters of a nonzero continuous form are unitary
-- statement:
--   Let $F$ be a number field, and for each infinite place $w$ of $F$ let $\chi_w$ be an arbitrary group homomorphism from the subgroup `rowIsometrySubgroup₀` of $\mathrm{GL}_2(F_w)$ (the completion $F_w$ being `w.Completion`) to $\mathbb{C}^\times$; no continuity of $\chi_w$ is assumed. Let $\varphi$ be a complex-valued function on `AdelicGL2 (𝓞 F) F`, the general linear group $\mathrm{GL}_2$ over the adele ring of $F$, and assume: $\varphi$ is continuous; $\varphi$ is not the zero function; and $\varphi$ lies in `archCutSubmodule F (ArchTypeFamily.ofChar F χ)`, i.e. in the intersection over all infinite places $w$ of the type submodule cut out, along the inclusion `rowIsometryInclAt₀ F w` of that local subgroup into the adelic group, by the one-dimensional representation `charRep (χ w)` on $\mathbb{C}^{\mathrm{Fin}\,1}$ given by scalar multiplication through $\chi_w$ (the type family `ofChar` has exactly one constituent, of dimension one, at each place). Then for every infinite place $w$ and every $k$ in `rowIsometrySubgroup₀ w.Completion` one has $\lvert\chi_w(k)\rvert = 1$.
--
--   This is the standard observation that the archimedean $K$-types occurring in a nonzero continuous automorphic form are unitary characters: boundedness of the form on a compact group forces the transformation character to take values on the unit circle. It is used in the analysis of cuspidal constituents, namely in [`AutomorphicForm.CuspidalConstituent.exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos`](thm.html#AutomorphicForm.CuspidalConstituent.exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_norm_archChar_eq_one_of_mem_archCutSubmodule_ofChar.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open AutomorphicForm

theorem AutomorphicForm.norm_archChar_eq_one_of_mem_archCutSubmodule_ofChar
    (F : Type) [Field F] [NumberField F]
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) (hne : φ ≠ 0)
    (hχ : φ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ)) :
    ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ‖((χ w k : ℂˣ) : ℂ)‖ = 1 := by sorry
