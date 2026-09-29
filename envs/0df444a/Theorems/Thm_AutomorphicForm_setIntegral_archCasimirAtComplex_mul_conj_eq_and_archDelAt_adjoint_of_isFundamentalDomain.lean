-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_archCasimirAtComplex_mul_conj_eq_and_archDelAt_adjoint_of_isFundamentalDomain
-- name    : AutomorphicForm.setIntegral_archCasimirAtComplex_mul_conj_eq_and_archDelAt_adjoint_of_isFundamentalDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/108c5c6c-1fc1-5816-b7dc-d7037f50ed88
-- title:
--   Adjointness of partial_X,partial̄_X and the Casimir operators at a complex place
-- statement:
--   Let $K$ be a number field, $w$ an infinite place of $K$ with `hw : w.IsComplex`, and let $0 < e_1 < e_2$ be reals. Let $\mathcal F$ be a measurable subset of $\mathrm{GL}_2$ of the adeles of $K$ contained in the slab $\{g : \mathrm{ideleNorm}_K(\det g) \in [e_1,e_2]\}$, where `ideleNorm` is the module of an idele given by its distributive Haar character, and assume $\mathcal F$ is a fundamental domain for the image of $\mathrm{GL}_2(K)$ under `globalPoints` (entrywise application of $K \to \mathbb A_K$) acting on the adelic Haar measure `adelicGLHaar` restricted to that slab. Let $x, x' : \mathrm{GL}_2(\mathbb A_K) \to \mathbb C$ be invariant under left translation by global points, continuous, smooth at $w$ in the sense of `IsArchSmoothAtComplex` (for each $g$, the map $e \mapsto x(g \cdot \mathrm{archComplexLiftAt}\,hw\,e)$ is $C^\infty$ on the set of invertible complex $2\times 2$ matrices $e$), with all flow derivatives `archDerivAtComplex` of order one and two along the six directions $H, E, F, iH, iE, iF$ continuous, and suppose a single real $B$ bounds $|x|, |x'|$ and all these first and second derivatives on the slab. Writing $\partial_X = \tfrac12(D_X - i D_{iX})$ (`archDelAt`), $\bar\partial_X = \tfrac12(D_X + i D_{iX})$ (`archDelBarAt`) for $X \in \{H,E,F\}$, $\Omega = -(\tfrac14\partial_H^2 - \tfrac12\partial_H + \partial_E\partial_F)$, $\bar\Omega$ the same expression in the $\bar\partial$'s, $p^+ = \partial_E + \bar\partial_F$ and $p^- = \partial_F + \bar\partial_E$, and $P(u,v) = \int_{\mathcal F} u\,\overline{v}\,d(\mathrm{adelicGLHaar})$, the conclusion is the conjunction of: $P(\partial_X x, x') = -P(x, \bar\partial_X x')$ and $P(\bar\partial_X x, x') = -P(x, \partial_X x')$ for all three $X$; $P(\Omega x, x') = P(x, \bar\Omega x')$ and $P(\bar\Omega x, x') = P(x, \Omega x')$; and $P(p^{+} x, x') = -P(x, p^{-} x')$, $P(p^{-} x, x') = -P(x, p^{+} x')$.
--
--   This records the Hermitian adjointness relations, with respect to the Petersson-type pairing over a fundamental domain inside a slab of bounded idele norm of the determinant, for the holomorphic and antiholomorphic Lie algebra directions at a complex place, for the two Casimir operators, and for the raising and lowering operators $p^{\pm}$. It is used in the analysis of cuspidal constituents at a complex place, to show that the eigenvalue of one Casimir operator is the complex conjugate of the other's and to bound the real part of a Casimir eigenvalue on a highest-weight vector.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_archCasimirAtComplex_mul_conj_eq_and_archDelAt_adjoint_of_isFundamentalDomain.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.setIntegral_archCasimirAtComplex_mul_conj_eq_and_archDelAt_adjoint_of_isFundamentalDomain
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
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
    (hxs : IsArchSmoothAtComplex hw x) (hx's : IsArchSmoothAtComplex hw x')
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD1' : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x'))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x)))
    (hD2' : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x')))
    (B : ℝ) (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ ‖x' g‖ ≤ B ∧
      (∀ d : ArchDirComplex, ‖archDerivAtComplex hw d x g‖ ≤ B ∧ ‖archDerivAtComplex hw d x' g‖ ≤ B) ∧
      (∀ d d' : ArchDirComplex,
        ‖archDerivAtComplex hw d (archDerivAtComplex hw d' x) g‖ ≤ B ∧
        ‖archDerivAtComplex hw d (archDerivAtComplex hw d' x') g‖ ≤ B)) :
    let pPlus : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun u => archDelAt hw .E u + archDelBarAt hw .Fm u
    let pMinus : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun u => archDelAt hw .Fm u + archDelBarAt hw .E u
    (∀ d : ArchDir,
      ∫ g in 𝓕, archDelAt hw d x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (archDelBarAt hw d x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∀ d : ArchDir,
      ∫ g in 𝓕, archDelBarAt hw d x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (archDelAt hw d x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, archCasimirAtComplex hw x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ∫ g in 𝓕, x g * conj (archCasimirBarAtComplex hw x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, archCasimirBarAtComplex hw x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ∫ g in 𝓕, x g * conj (archCasimirAtComplex hw x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, pPlus x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (pMinus x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, pMinus x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (pPlus x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by sorry
