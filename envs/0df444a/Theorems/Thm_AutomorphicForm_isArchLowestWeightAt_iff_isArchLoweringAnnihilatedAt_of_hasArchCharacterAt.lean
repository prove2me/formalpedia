-- Prove2me | Theorems.Thm_AutomorphicForm_isArchLowestWeightAt_iff_isArchLoweringAnnihilatedAt_of_hasArchCharacterAt
-- name    : AutomorphicForm.isArchLowestWeightAt_iff_isArchLoweringAnnihilatedAt_of_hasArchCharacterAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/ac8fd646-51dc-5a02-ae7b-9ac94f7134a3
-- title:
--   Lowest weight at a real place versus lowering annihilation
-- statement:
--   Let $F$ be a number field, $w$ a real infinite place of $F$ with witness $hw$ of reality, $k \in \mathbb{Z}$, and let $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a continuous function on the adelic group $\mathrm{GL}_2$ of the adele ring of $F$. Assume that $\varphi$ satisfies `HasArchCharacterAt₀` at $w$ for the character obtained by composing the weight-$k$ character `archWeightCharℝ k` with the transport map `rowIsometrySubgroup₀Map` along the isomorphism $F_w \cong \mathbb{R}$ coming from `ringEquivRealOfIsReal hw` and its norm-compatibility, i.e. $\varphi$ is of weight $k$ under the row-isometry subgroup at $w$. Assume further given a group homomorphism $\xi$ from the full group of ideles $(\mathbb{A}_F)^{\times}$ (as the subgroup $\top$) to $\mathbb{C}^{\times}$ such that $\varphi(\mathrm{scal}(z)\,g) = \xi(z)\,\varphi(g)$ for every idele $z$ and every $g$, where $\mathrm{scal}$ is the central embedding `centralScalar` of $(\mathbb{A}_F)^{\times}$ into $\mathrm{GL}_2(\mathbb{A}_F)$ as scalar matrices. Then `IsArchLowestWeightAt w hw φ` holds if and only if `IsArchLoweringAnnihilatedAt w hw φ` holds. The first condition says: there exists $\sigma \in \mathbb{C}$ such that for every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ the function $z \mapsto (\operatorname{Im} z)^{\sigma}\,\varphi\bigl(g \cdot \iota_w(\begin{smallmatrix} \operatorname{Im} z & \operatorname{Re} z \\ 0 & 1\end{smallmatrix})\bigr)$ on the upper half-plane is holomorphic (`MDifferentiable` for the complex model on source and target), where the Iwasawa section matrix `iwasawaSectionGL z` is carried into $\mathrm{GL}_2(F_w)$ along $\mathbb{R} \cong F_w$ and then into the adelic group by `adelicArchGLInclAt F w`. The second says: for every $g$ and every $z$ in the upper half-plane, the archimedean slice $m \mapsto \varphi\bigl(g\cdot\iota_w(m)\bigr)$ for $m$ of nonzero determinant (and $0$ otherwise), as a function on $2\times 2$ real matrices, is real-differentiable at $\bigl(\begin{smallmatrix} \operatorname{Im} z & \operatorname{Re} z \\ 0 & 1\end{smallmatrix}\bigr)$ and is annihilated there by the lowering operator $f \mapsto \tfrac{1}{2}\bigl(Df(m)(m\,\mathrm{diag}(1,-1)) - i\,Df(m)(m\,(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}))\bigr)$.
--
--   This is the Maass-operator dictionary at a real place, transcribed for functions on the adelic group: a vector of weight $k$ under the row-isometry subgroup at $w$, with a central character, has holomorphic archimedean descents after renormalisation by a power of the imaginary part exactly when its slices are killed by the weight-lowering operator. It feeds the reformulation of lowering-annihilation in terms of smoothness together with vanishing of the lowering operator, and the characterisation of occurrence of $K$-types in the archimedean class of such a function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isArchLowestWeightAt_iff_isArchLoweringAnnihilatedAt_of_hasArchCharacterAt.lean

import Definitions.Def_AutomorphicForm_ArchLowestWeight
import Definitions.Def_AutomorphicForm_ArchLoweringAnnihilated

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.isArchLowestWeightAt_iff_isArchLoweringAnnihilatedAt_of_hasArchCharacterAt
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal) (k : ℤ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hk : HasArchCharacterAt₀ F w
      ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
        (norm_ringEquivRealOfIsReal hw))) φ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξ : ∀ (z : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ)) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g) :
    IsArchLowestWeightAt w hw φ ↔ IsArchLoweringAnnihilatedAt w hw φ := by sorry
