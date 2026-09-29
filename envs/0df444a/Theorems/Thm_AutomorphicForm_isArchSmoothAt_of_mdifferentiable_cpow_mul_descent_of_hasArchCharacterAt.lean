-- Prove2me | Theorems.Thm_AutomorphicForm_isArchSmoothAt_of_mdifferentiable_cpow_mul_descent_of_hasArchCharacterAt
-- name    : AutomorphicForm.isArchSmoothAt_of_mdifferentiable_cpow_mul_descent_of_hasArchCharacterAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/4a6d619f-75b1-5575-b6fb-91834b35e921
-- title:
--   Archimedean smoothness from holomorphy of Iwasawa descents
-- statement:
--   Let $F$ be a number field, let $w$ be an infinite place of $F$ assumed real, and let $\varphi$ be a complex-valued function on `AdelicGL2 (𝓞 F) F`, the group $\mathrm{GL}_2$ over the adele ring of $F$. Fix $k \in \mathbb{Z}$ and $c_0, \sigma \in \mathbb{C}$. Write $\iota_w$ for `adelicArchGLInclAt F w`, the embedding of $\mathrm{GL}_2$ of the completion at $w$ into the adelic group through the infinite adeles (trivial in the finite component), and use the ring isomorphism `ringEquivRealOfIsReal hw` between that completion and $\mathbb{R}$. The hypotheses are: (i) $\varphi$ satisfies `HasArchCharacterAt₀ F w (archWeightCharAt hw k) φ`, expressing that $\varphi$ transforms at $w$ under the character `archWeightCharAt hw k` of `rowIsometrySubgroup₀` of the completion, namely the $k$-th power of `archWeightOneAt hw`, which is `archWeightOneℝ` transported along the identification of the completion with $\mathbb{R}$; (ii) for every unit $t$ of $\mathbb{R}$ with $t > 0$ and every $g$, one has $\varphi(\iota_w(t \cdot 1) \, g) = t^{c_0} \varphi(g)$, the power being the complex power of the real number $t$; (iii) for every $g$, the function $z \mapsto (\operatorname{Im} z)^{\sigma} \, \varphi\bigl(g \, \iota_w(\mathrm{iwasawaSectionGL}\, z)\bigr)$, where `iwasawaSectionGL z` is the matrix $\begin{pmatrix} \operatorname{Im} z & \operatorname{Re} z \\ 0 & 1\end{pmatrix}$ in $\mathrm{GL}_2(\mathbb{R})$, is differentiable as a map of complex manifolds from the upper half-plane to $\mathbb{C}$. The conclusion is `IsArchSmoothAt hw φ`: for every $g$, the map sending a real $2 \times 2$ array $e$ to $\varphi(g \cdot \mathrm{archRealLiftAt}\ hw\ e)$, where `archRealLiftAt hw e` is the image at $w$ of $e$ when $\det e \neq 0$ and $1$ otherwise, is $C^{\infty}$ on the set $\{e \mid \det e \neq 0\}$.
--
--   This is the regularity statement in the passage between adelic functions with prescribed behaviour at a real place and classical holomorphic data on the upper half-plane: rotation type $k$, the scalar exponent $c_0$ and holomorphy of the renormalised Iwasawa descents together force smoothness in the archimedean variable at $w$. It is used in [`AutomorphicForm.isArchLowestWeightAt_iff_and_isArchHolomorphicAt_iff_lower_eq_zero_of_hasArchCharacterAt`](thm.html#AutomorphicForm.isArchLowestWeightAt_iff_and_isArchHolomorphicAt_iff_lower_eq_zero_of_hasArchCharacterAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isArchSmoothAt_of_mdifferentiable_cpow_mul_descent_of_hasArchCharacterAt.lean

import Definitions.Def_AutomorphicForm_ArchLowestWeight
import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Manifold

theorem AutomorphicForm.isArchSmoothAt_of_mdifferentiable_cpow_mul_descent_of_hasArchCharacterAt
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (k : ℤ) (c₀ σ : ℂ)
    (hk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) φ)
    (hc : ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
      φ (adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ c₀) * φ g)
    (hσ : ∀ g : AdelicGL2 (𝓞 F) F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
      (((z.im : ℝ) : ℂ) ^ σ) * φ (g * adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (iwasawaSectionGL z)))) :
    IsArchSmoothAt hw φ := by sorry
