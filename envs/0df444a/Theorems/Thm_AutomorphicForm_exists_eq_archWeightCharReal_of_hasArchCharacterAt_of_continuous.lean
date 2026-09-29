-- Prove2me | Theorems.Thm_AutomorphicForm_exists_eq_archWeightCharReal_of_hasArchCharacterAt_of_continuous
-- name    : AutomorphicForm.exists_eq_archWeightCharReal_of_hasArchCharacterAt_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/35d73b1e-0528-58ac-84fd-451563723923
-- title:
--   Archimedean characters at a real place are integral weight characters
-- statement:
--   Let $F$ be a number field, $w$ an infinite place of $F$ with `hw : w.IsReal`, and let $\chi$ be a group homomorphism from `rowIsometrySubgroup₀ ℝ` to $\mathbb C^\times$; here `rowIsometrySubgroup₀` is the subscript-zero variant, for a normed field, of the row-isometry subgroup `rowIsometrySubgroup` of $\mathrm{GL}_2$, whose elements are the invertible $2\times 2$ matrices $k$ with $\|\det k\| = 1$ such that $\|xk_{00}+yk_{10}\|^2+\|xk_{01}+yk_{11}\|^2 = \|x\|^2+\|y\|^2$ for all $x,y$. Let $\varphi$ be a continuous complex-valued function on `AdelicGL2 (𝓞 F) F`, that is on $\mathrm{GL}_2$ of the adele ring of $F$, and assume $\varphi$ is not identically zero, i.e. $\varphi(g)\neq 0$ for some $g$. Assume further `HasArchCharacterAt₀ F w` holds for $\varphi$ and for the character obtained by composing $\chi$ with the map `rowIsometrySubgroup₀Map` induced by the norm-preserving ring isomorphism `ringEquivRealOfIsReal hw` from the completion $F_w$ to $\mathbb R$; this is the subscript-zero analogue of `HasArchCharacterAt`, which asserts $\varphi(g\cdot \iota_w(k)) = \chi(k)\,\varphi(g)$ for all $k$ in the subgroup at $w$ and all $g$, where $\iota_w$ is `adelicArchGLInclAt F w`, the inclusion of $\mathrm{GL}_2(F_w)$ into $\mathrm{GL}_2(\mathbb A_F)$. Then there exists an integer $n$ with $\chi =$ `archWeightCharℝ n`, the weight-$n$ character.
--
--   This is the classical rigidity statement that a character of the rotation group $\mathrm{SO}(2,\mathbb R)$ which is carried by a nonzero continuous function on $\mathrm{GL}_2(\mathbb A_F)$ is automatically continuous, hence of the form $r(\theta)\mapsto e^{in\theta}$ for some $n \in \mathbb Z$. It is used in the analysis of archimedean types at a real place, in [`AutomorphicForm.archOccursInClassOf_archWeightChar_iff_parity_or_discreteSeries_of_coversModCentre`](thm.html#AutomorphicForm.archOccursInClassOf_archWeightChar_iff_parity_or_discreteSeries_of_coversModCentre) and [`AutomorphicForm.archOccursInClassOf_iff_archCasimirAt_of_coversModCentre`](thm.html#AutomorphicForm.archOccursInClassOf_iff_archCasimirAt_of_coversModCentre), to reduce arbitrary archimedean characters to integral weights.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_eq_archWeightCharReal_of_hasArchCharacterAt_of_continuous.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.InfinitePlace
  NumberField.InfinitePlace.Completion

theorem AutomorphicForm.exists_eq_archWeightCharReal_of_hasArchCharacterAt_of_continuous
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (χ : rowIsometrySubgroup₀ ℝ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hφ0 : ∃ g : AdelicGL2 (𝓞 F) F, φ g ≠ 0)
    (hχ : HasArchCharacterAt₀ F w
      (χ.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)))
      φ) :
    ∃ n : ℤ, χ = archWeightCharℝ n := by sorry
