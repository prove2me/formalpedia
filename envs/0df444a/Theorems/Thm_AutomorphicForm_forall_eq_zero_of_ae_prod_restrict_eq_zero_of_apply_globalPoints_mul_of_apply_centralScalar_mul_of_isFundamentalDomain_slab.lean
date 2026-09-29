-- Prove2me | Theorems.Thm_AutomorphicForm_forall_eq_zero_of_ae_prod_restrict_eq_zero_of_apply_globalPoints_mul_of_apply_centralScalar_mul_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.forall_eq_zero_of_ae_prod_restrict_eq_zero_of_apply_globalPoints_mul_of_apply_centralScalar_mul_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/fb1f2cb5-7572-5b21-b8bb-49821de8f57f
-- title:
--   Bi-automorphic kernels vanishing a.e. on Φ×Φ vanish
-- statement:
--   Let $K$ be a number field, and let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$. Write $\mathbb{A}$ for the adele ring of $K$, $G=\mathrm{GL}_2(\mathbb{A})$ (the group `AdelicGL2 (𝓞 K) K`) equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`, and $\|x\|$ for the idele norm, the value at $x$ of the distributive Haar character of $\mathbb{A}$. Let $S=\{g\in G:\|\det g\|\in[\alpha,\beta]\}$ be the determinant slab, and let $\Phi\subseteq S$ be a fundamental domain, in Mathlib's almost-everywhere sense, for the action of the image of $\mathrm{GL}_2(K)$ in $G$ under the entrywise map induced by $K\to\mathbb{A}$, with respect to Haar measure restricted to $S$. Let $F:G\times G\to\mathbb{C}$ be separately continuous, i.e. continuous in the first variable for each fixed second variable and conversely; invariant under left multiplication of either variable by any $\gamma\in\mathrm{GL}_2(K)$; and such that the vanishing of $F(x,y)$ is preserved by left multiplication of either variable by the central scalar matrix attached to any idele $z\in\mathbb{A}^\times$. If $F(p_1,p_2)=0$ for almost every $p$ with respect to the product of two copies of Haar measure restricted to $\Phi$, then $F(x,y)=0$ for all $x,y\in G$.
--
--   This is the standard passage from an almost-everywhere identity of kernels on a fundamental domain to a pointwise identity, for functions on $\mathrm{GL}_2(\mathbb{A})\times\mathrm{GL}_2(\mathbb{A})$ that are automorphic in each variable separately. It is used to upgrade the almost-everywhere form of the spectral expansion to its pointwise form, and is cited in the derivation of the pointwise expansion of the relevant integral operators and in the vanishing statement for axis continuations with vanishing constant terms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_eq_zero_of_ae_prod_restrict_eq_zero_of_apply_globalPoints_mul_of_apply_centralScalar_mul_of_isFundamentalDomain_slab.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.forall_eq_zero_of_ae_prod_restrict_eq_zero_of_apply_globalPoints_mul_of_apply_centralScalar_mul_of_isFundamentalDomain_slab
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (F : AdelicGL2 (𝓞 K) K → AdelicGL2 (𝓞 K) K → ℂ)
    (hFx : ∀ y : AdelicGL2 (𝓞 K) K, Continuous fun x : AdelicGL2 (𝓞 K) K => F x y)
    (hFy : ∀ x : AdelicGL2 (𝓞 K) K, Continuous fun y : AdelicGL2 (𝓞 K) K => F x y)
    (hΓx : ∀ (γ : GL (Fin 2) K) (x y : AdelicGL2 (𝓞 K) K), F (globalPoints (𝓞 K) K γ * x) y = F x y)
    (hΓy : ∀ (γ : GL (Fin 2) K) (x y : AdelicGL2 (𝓞 K) K), F x (globalPoints (𝓞 K) K γ * y) = F x y)
    (hZx : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (x y : AdelicGL2 (𝓞 K) K), F x y = 0 → F (centralScalar (𝓞 K) K z * x) y = 0)
    (hZy : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (x y : AdelicGL2 (𝓞 K) K), F x y = 0 → F x (centralScalar (𝓞 K) K z * y) = 0)
    (hae : ∀ᵐ p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K
      ∂(((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ).prod ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ)),
      F p.1 p.2 = 0) :
    ∀ x y : AdelicGL2 (𝓞 K) K, F x y = 0 := by sorry
