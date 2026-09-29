-- Prove2me | Theorems.Thm_AutomorphicForm_foldr_archDeriv_mul_eq_of_forall_mul_eq
-- name    : AutomorphicForm.foldr_archDeriv_mul_eq_of_forall_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/c49bd4ee-3543-594f-ad17-fd5fb2479cd7
-- title:
--   Words in archimedean derivations preserve level invariance and central characters
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal{O}_K$, let $N$ be an ideal of $\mathcal{O}_K$, and work on the group $\mathrm{GL}_2$ of the adele ring of $K$. Fix families of characters $\omega_{\mathbb R,w} : \mathbb{R}^\times \to \mathbb{C}^\times$ indexed by the real infinite places $w$ of $K$ and $\omega_{\mathbb C,w} : \mathbb{C}^\times \to \mathbb{C}^\times$ indexed by the complex ones, and let $b$ be a complex-valued function on $\mathrm{GL}_2(\mathbb{A}_K)$ such that: (i) $b(gu) = b(g)$ for all $g$ and all $u$ in the intersection of `principalLevel` at $N$ (the subgroup `levelOne` at $N$ intersected with its conjugate by `weyl`) with `finiteAdelicGL2Subgroup`, the kernel of the map to $\mathrm{GL}_2$ of the infinite adeles; (ii) at each real place $w$, $b(g\,\iota_w(\mathrm{diag}(t,t))) = \omega_{\mathbb R,w}(t)\,b(g)$ for $t \in \mathbb{R}^\times$, where $\iota_w$ is `archRealGLAt`; (iii) at each complex place, the analogous identity with $\omega_{\mathbb C,w}$ and `archComplexGLAt`. Let $W$ send a list of labels — each either a real place with a direction in $\{H,E,F\}$ or a complex place with one of six directions — and a function to the right-fold iterate of the corresponding invariant derivations `archDerivAt`, `archDerivAtComplex` (derivatives at $t=0$ of right translation along the one-parameter flows). The conclusion asserts that for every such list $l$, the function $W\,l\,b$ again satisfies (i), (ii) and (iii) with the same characters.
--
--   This records that the space of functions with a fixed finite level and fixed archimedean central characters is stable under arbitrary words in the invariant differential operators attached to the infinite places, the right translations involved commuting with those operators. It is used in the sup-norm estimate [`AutomorphicForm.exists_isCompact_forall_norm_le_mul_of_forall_eLpNorm_foldr_archDeriv_le`](thm.html#AutomorphicForm.exists_isCompact_forall_norm_le_mul_of_forall_eLpNorm_foldr_archDeriv_le), where Sobolev-type bounds on iterated derivatives are transported through charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_foldr_archDeriv_mul_eq_of_forall_mul_eq.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.InfinitePlace
open AutomorphicForm
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.foldr_archDeriv_mul_eq_of_forall_mul_eq
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K))
    (ωR : ∀ w : InfinitePlace K, w.IsReal → (ℝˣ →* ℂˣ))
    (ωC : ∀ w : InfinitePlace K, w.IsComplex → (ℂˣ →* ℂˣ))
    (b : AdelicGL2 (𝓞 K) K → ℂ)
    (hbU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, b (g * u) = b g)
    (hbR : ∀ (w : InfinitePlace K) (hw : w.IsReal) (t : ℝˣ) (g : AdelicGL2 (𝓞 K) K),
        b (g * archRealGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom t)) =
          ((ωR w hw t : ℂˣ) : ℂ) * b g)
    (hbC : ∀ (w : InfinitePlace K) (hw : w.IsComplex) (z : ℂˣ) (g : AdelicGL2 (𝓞 K) K),
        b (g * archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom z)) =
          ((ωC w hw z : ℂˣ) : ℂ) * b g) :
    let W : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) →
        (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun l b => l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ)
        (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b
    ∀ l, (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, W l b (g * u) = W l b g) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal) (t : ℝˣ) (g : AdelicGL2 (𝓞 K) K),
        W l b (g * archRealGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom t)) =
          ((ωR w hw t : ℂˣ) : ℂ) * W l b g) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex) (z : ℂˣ) (g : AdelicGL2 (𝓞 K) K),
        W l b (g * archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom z)) =
          ((ωC w hw z : ℂˣ) : ℂ) * W l b g) := by sorry
