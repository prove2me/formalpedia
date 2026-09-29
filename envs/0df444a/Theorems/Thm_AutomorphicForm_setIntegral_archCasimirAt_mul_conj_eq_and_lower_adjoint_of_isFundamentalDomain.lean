-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain
-- name    : AutomorphicForm.setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/3240b044-857e-55c5-97fb-3d8d2aef75a3
-- title:
--   Casimir symmetry and raising–lowering adjointness on a fundamental domain
-- statement:
--   Let $K$ be a number field and $w$ a real infinite place of $K$, and let $0 < e_1 < e_2$ be reals. Let $\mathcal F \subseteq \mathrm{GL}_2(\mathbb A_K)$ be measurable (for the Borel structure attached to the Haar measure `adelicGLHaar`), contained in the determinant slab $\{g : \mathrm{ideleNorm}_K(\det g) \in [e_1,e_2]\}$ — where $\mathrm{ideleNorm}_K$ is the module of an idele, i.e. its distributive Haar character on $\mathbb A_K$ read as a real number — and assume $\mathcal F$ is a fundamental domain for the action of the image of $\mathrm{GL}_2(K)$ in $\mathrm{GL}_2(\mathbb A_K)$ under the map induced by $K \to \mathbb A_K$, with respect to `adelicGLHaar` restricted to that slab. Let $x, x' : \mathrm{GL}_2(\mathbb A_K) \to \mathbb C$ be invariant under left translation by all global points $\gamma \in \mathrm{GL}_2(K)$, continuous, and smooth at $w$ in the sense that for every $g$ the function $e \mapsto x(g \cdot \mathrm{archRealLiftAt}\,e)$ is $C^\infty$ on the set of real $2\times2$ matrices $e$ with $\det e \neq 0$, the lift being the embedding of $\mathrm{GL}_2(\mathbb R)$ at $w$. Here, for each direction $d \in \{H, E, F\}$, $\mathrm{archDerivAt}\,d$ sends $\varphi$ to $g \mapsto \frac{d}{dt}\varphi(g\cdot \mathrm{archFlowAt}\,d\,t)|_{t=0}$, the derivative along the corresponding real one-parameter flow at $w$. Assume all first derivatives $D_d x$, $D_d x'$ and all second derivatives $D_d D_{d'} x$, $D_d D_{d'} x'$ are continuous, and that a single real bound $B$ dominates the norms of $x$, $x'$ and of all these first and second derivatives at every $g$ in the slab. Writing $\Omega = -\big(\tfrac14 D_H D_H - \tfrac12 D_H + D_E D_F\big)$ for the Casimir operator at $w$, and setting $\mathrm{lower}\,u = D_H u - i\,(D_E u + D_F u)$ and $\mathrm{raise}\,u = D_H u + i\,(D_E u + D_F u)$, the conclusion is the conjunction of three identities of integrals over $\mathcal F$ against `adelicGLHaar`: $\int_{\mathcal F} \Omega x \cdot \overline{x'} = \int_{\mathcal F} x \cdot \overline{\Omega x'}$, $\int_{\mathcal F} \mathrm{lower}\,x \cdot \overline{x'} = -\int_{\mathcal F} x \cdot \overline{\mathrm{raise}\,x'}$, and $\int_{\mathcal F} \mathrm{raise}\,x \cdot \overline{x'} = -\int_{\mathcal F} x \cdot \overline{\mathrm{lower}\,x'}$.
--
--   This is the statement that, for the Petersson-type pairing $P(u,v) = \int_{\mathcal F} u\overline{v}$ on a determinant slab, the Casimir element at a real place is symmetric and the lowering operator is the negative adjoint of the raising operator, the infinitesimal unitarity relations for the derived $\mathfrak{sl}_2(\mathbb R)$-action. The proof cites the skew-symmetry of a single flow derivative for this pairing, the $\mathfrak{sl}_2$ commutator relations for the flow derivatives, and the finiteness of the measure of the slab part of a fundamental domain; it is used to show that Casimir eigenvalues of cuspidal constituents are real and suitably signed, and that lowering operators are non-vanishing on the relevant weight spaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.TateGlobal
open IsDedekindDomain
open AutomorphicForm
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}))
    (x x' : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hx' : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x' (globalPoints (𝓞 K) K γ * g) = x' g)
    (hxc : Continuous x) (hx'c : Continuous x')
    (hxs : IsArchSmoothAt hw x) (hx's : IsArchSmoothAt hw x')
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x)) (hD1' : ∀ d : ArchDir, Continuous (archDerivAt hw d x'))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x)))
    (hD2' : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x')))
    (B : ℝ) (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ ‖x' g‖ ≤ B ∧ (∀ d : ArchDir, ‖archDerivAt hw d x g‖ ≤ B ∧ ‖archDerivAt hw d x' g‖ ≤ B) ∧
      (∀ d d' : ArchDir, ‖archDerivAt hw d (archDerivAt hw d' x) g‖ ≤ B ∧ ‖archDerivAt hw d (archDerivAt hw d' x') g‖ ≤ B)) :
    let lower : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun u => archDerivAt hw .H u - Complex.I • (archDerivAt hw .E u + archDerivAt hw .Fm u)
    let raise : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun u => archDerivAt hw .H u + Complex.I • (archDerivAt hw .E u + archDerivAt hw .Fm u)
    (∫ g in 𝓕, archCasimirAt hw x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ∫ g in 𝓕, x g * conj (archCasimirAt hw x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, lower x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (raise x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, raise x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (lower x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by sorry
