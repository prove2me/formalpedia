-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isFactorizableTestFn_hasArchCharacterAt_rightConv_ne_zero_of_hasArchCharacterAt
-- name    : AutomorphicForm.exists_isFactorizableTestFn_hasArchCharacterAt_rightConv_ne_zero_of_hasArchCharacterAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/5b61db7e-6143-5789-89c9-dbbd5216c80c
-- title:
--   Level-adapted test function preserving the archimedean type at w
-- statement:
--   Let $K$ be a number field, $N \neq 0$ an ideal of $\mathcal{O}_K$, $w$ a real infinite place of $K$ and $k$ an integer; write $U =$ `levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` for the subgroup of $\mathrm{GL}_2(\mathbb{A}_K)$ consisting of those $u$ whose archimedean component `glArch` is trivial and whose finite component `glFin` lies in `finiteLevelOne` at $N$, and let $\chi$ be the character of the archimedean row-isometry group at $w$ obtained from `archWeightCharℝ k` by transport along the norm-preserving isomorphism $K_w \cong \mathbb{R}$ given by `ringEquivRealOfIsReal hw`. Assume $\varphi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ is continuous, nonzero at some point, satisfies $\varphi(gu) = \varphi(g)$ for all $g$ and all $u \in U$, and satisfies `HasArchCharacterAt₀ K w` for the character $\chi$. Then there is $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ which is a factorizable test function, i.e. $f(g) = f_\infty(\mathrm{glArch}\, g) \cdot f_{\mathrm{fin}}(\mathrm{glFin}\, g)$ with $f_\infty$ a compactly supported smooth function of the archimedean matrix entries and $f_{\mathrm{fin}}$ locally constant with compact support, such that $f(ux) = f(x)$ for all $u \in U$ and all $x$; every $x$ with $f(x) \neq 0$ factors as $x = au$ with $\mathrm{glFin}\, a = 1$ and $u \in U$; the right convolution $g \mapsto \int \varphi(gx) f(x)\, dx$ against the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$ again satisfies `HasArchCharacterAt₀ K w` for $\chi$; and this convolution is nonzero at some point.
--
--   This is the refinement, keeping track of the weight-$k$ type at one real place, of the standard smoothing step: a continuous level-invariant function is not annihilated by convolution against a suitable approximate identity adapted to the level. It is used in the analysis of which archimedean types occur in the automorphic class of a given form, in particular by the lemmas on occurrence of `archWeightChar` and on lowering-annihilated types.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isFactorizableTestFn_hasArchCharacterAt_rightConv_ne_zero_of_hasArchCharacterAt.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm NumberField.InfinitePlace
  NumberField.InfinitePlace.Completion

theorem AutomorphicForm.exists_isFactorizableTestFn_hasArchCharacterAt_rightConv_ne_zero_of_hasArchCharacterAt
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (w : InfinitePlace K) (hw : w.IsReal) (k : ℤ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ) (hne : ∃ g, φ g ≠ 0)
    (hlev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      φ (g * u) = φ g)
    (hk : HasArchCharacterAt₀ K w
      ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
        (norm_ringEquivRealOfIsReal hw))) φ) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ,
      IsFactorizableTestFn K f ∧
      (∀ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ∀ x, f (u * x) = f x) ∧
      (∀ x, f x ≠ 0 → ∃ a u : AdelicGL2 (𝓞 K) K,
        glFin (𝓞 K) K a = 1 ∧ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧ x = a * u) ∧
      HasArchCharacterAt₀ K w
        ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
          (norm_ringEquivRealOfIsReal hw))) (rightConv K φ f) ∧
      ∃ g, rightConv K φ f g ≠ 0 := by sorry
