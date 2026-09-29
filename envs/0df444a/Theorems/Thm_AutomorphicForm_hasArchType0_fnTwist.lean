-- Prove2me | Theorems.Thm_AutomorphicForm_hasArchType0_fnTwist
-- name    : AutomorphicForm.hasArchType0_fnTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/360e7ed9-b37a-5a73-952b-c95cb267444d
-- title:
--   Determinant twists preserve archimedean type χ
-- statement:
--   Let $F$ be a number field (a field with a `NumberField` instance), let $\eta$ be a monoid homomorphism from the unit group $(\mathbb{A}_F)^\times$ of the adele ring `AdeleRing (𝓞 F) F` to $\mathbb{C}^\times$, and let $\chi$ assign to each infinite place $w$ of $F$ a monoid homomorphism $\chi_w$ from the group `rowIsometrySubgroup₀ w.Completion` of matrices in $\mathrm{GL}_2(F_w)$ to $\mathbb{C}^\times$; elements of this group have determinant exactly $1$, by `mem_rowIsometrySubgroup₀_iff`. Let $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a function on `AdelicGL2 (𝓞 F) F`, the general linear group of $2\times 2$ matrices over the adele ring. The hypothesis is that $\varphi$ satisfies the predicate `HasArchType₀ F χ φ`, the archimedean-type condition relative to the family $\chi$ and the groups `rowIsometrySubgroup₀ w.Completion`, a statement quantified over an infinite place $w$, an element $k$ of that group and a point $g$ of $\mathrm{GL}_2(\mathbb{A}_F)$ (the analogue, for these subgroups, of `HasArchType`, which asserts $\varphi(g \cdot \iota_w(k)) = \chi_w(k)\,\varphi(g)$ for the embedding `adelicArchGLInclAt F w` of $\mathrm{GL}_2(F_w)$ at $w$). The conclusion is that the twist `fnTwist F η φ`, namely $g \mapsto \eta(\det g)\,\varphi(g)$ with $\eta \circ \det$ taken through `chiDet`, satisfies the same condition `HasArchType₀ F χ` with the same family $\chi$.
--
--   This is the standard observation that multiplying a function on $\mathrm{GL}_2(\mathbb{A}_F)$ by a character of the determinant does not change its type under the determinant-one row-isometry groups at the infinite places, since those groups lie in the kernel of the determinant. It is used in the comparison of adelic spans for newforms and their determinant twists, in [`CuspForm.IsNewform.adelicSpanSubmodule_eq_of_isPrimitiveForm_adelicLiftGamma1_fnTwist`](thm.html#CuspForm.IsNewform.adelicSpanSubmodule_eq_of_isPrimitiveForm_adelicLiftGamma1_fnTwist).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_hasArchType0_fnTwist.lean

import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_AutomorphicForm_FnTwist

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.hasArchType0_fnTwist
    (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : HasArchType₀ F χ φ) :
    HasArchType₀ F χ (fnTwist F η φ) := by sorry
