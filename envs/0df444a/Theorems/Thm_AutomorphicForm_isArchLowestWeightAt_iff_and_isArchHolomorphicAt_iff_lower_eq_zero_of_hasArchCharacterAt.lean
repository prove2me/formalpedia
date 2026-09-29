-- Prove2me | Theorems.Thm_AutomorphicForm_isArchLowestWeightAt_iff_and_isArchHolomorphicAt_iff_lower_eq_zero_of_hasArchCharacterAt
-- name    : AutomorphicForm.isArchLowestWeightAt_iff_and_isArchHolomorphicAt_iff_lower_eq_zero_of_hasArchCharacterAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/96c0a83b-6a35-521c-9a2d-525566705a5f
-- title:
--   Lowest weight and y⁻¹-holomorphy via the lowering operator
-- statement:
--   Let $F$ be a number field, $w$ an infinite place of $F$ with `hw : w.IsReal`, and $\varphi$ a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $F$; let $k$ be an integer and $c_0$ a complex number. Assume that $\varphi$ has the character `archWeightCharAt hw k` at $w$ in the sense of the predicate `HasArchCharacterAt₀`, where `archWeightCharAt hw k` is the $k$-th power of the character `archWeightOneAt hw` of the rotation-type subgroup `rowIsometrySubgroup₀` of $\mathrm{GL}_2(w\text{-completion})$, and assume the central homogeneity hypothesis: for every real unit $t$ with $t>0$ and every $g$, left translation by the image under `adelicArchGLInclAt F w` of the scalar matrix $t$ (transported along the inverse of the identification `ringEquivRealOfIsReal hw` of $w$'s completion with $\mathbb R$) multiplies $\varphi(g)$ by $t^{c_0}$. Write $L\varphi := D_H\varphi - i\,(D_E\varphi + D_{F}\varphi)$, where $D_d\varphi(g)$ is the derivative at $t=0$ of $t\mapsto \varphi(g\cdot\,$`archFlowAt hw d t`$)$ for $d \in \{H,E,F_{-}\}$, and call $\varphi$ smooth at $w$ when, for each $g$, the map $e\mapsto\varphi(g\cdot\,$`archRealLiftAt hw e`$)$ is $C^\infty$ on the set of real $2\times 2$ matrices of nonzero determinant. Then two equivalences hold. First: there exists $\sigma\in\mathbb C$ such that for every $g$ the descent $z\mapsto(\operatorname{Im}z)^{\sigma}\varphi(g\cdot$ `adelicArchGLInclAt F w` applied to `iwasawaSectionGL z` transported along `ringEquivRealOfIsReal hw`$^{-1})$ is holomorphic on the upper half-plane, if and only if $\varphi$ is smooth at $w$ and $L\varphi = 0$. Second: all the $\sigma=-1$ descents $z\mapsto(\operatorname{Im}z)^{-1}\varphi(g\cdot\iota_w($`iwasawaSectionGL z`$))$ are holomorphic if and only if $\varphi$ is smooth at $w$, $L\varphi=0$, and $(k+c_0-2)\cdot\varphi = 0$.
--
--   This is the Maass-style bridge between the complex-analytic description of a lowest-weight vector at a real place (holomorphy of the $y^{\sigma}$-normalised descents) and its infinitesimal description (smoothness together with annihilation by the lowering operator), the normalisation $\sigma = -1$ corresponding to $k+c_0=2$. It is used in the passage between the Casimir/occurrence formulation of the archimedean type and the lowering-operator formulation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isArchLowestWeightAt_iff_and_isArchHolomorphicAt_iff_lower_eq_zero_of_hasArchCharacterAt.lean

import Definitions.Def_AutomorphicForm_ArchLowestWeight
import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Manifold

theorem AutomorphicForm.isArchLowestWeightAt_iff_and_isArchHolomorphicAt_iff_lower_eq_zero_of_hasArchCharacterAt
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (k : ℤ) (c₀ : ℂ)
    (hk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) φ)
    (hc : ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
      φ (adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ c₀) * φ g) :
    (IsArchLowestWeightAt w hw φ ↔
      IsArchSmoothAt hw φ ∧
        archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) = 0) ∧
    (IsArchHolomorphicAt w hw φ ↔
      IsArchSmoothAt hw φ ∧
        archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) = 0 ∧
        ((k : ℂ) + c₀ - 2) • φ = 0) := by sorry
