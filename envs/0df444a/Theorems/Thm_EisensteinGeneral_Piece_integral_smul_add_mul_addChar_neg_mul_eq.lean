-- Prove2me | Theorems.Thm_EisensteinGeneral_Piece_integral_smul_add_mul_addChar_neg_mul_eq
-- name    : EisensteinGeneral.Piece.integral_smul_add_mul_addChar_neg_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/de0c2d03-b413-516f-93f6-809888afa627
-- title:
--   Affine change of variables in a twisted adelic integral
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$, and equip the adele ring $\mathbb{A}_F$ of $F$ with the Borel $\sigma$-algebra of its topology (`adelicBorel`), so that it is a Borel space and carries the additive Haar measure `adelicAddHaar` defined as `Measure.addHaar`. Let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$, let $f : \mathbb{A}_F \to \mathbb{C}$ be an arbitrary function (no measurability or integrability is assumed), let $a$ be a unit of $\mathbb{A}_F$, i.e. an idele, and let $u, \xi \in \mathbb{A}_F$. Then
--   $$\int_{\mathbb{A}_F} f(a\cdot(y+u))\,\psi(-(\xi y))\,dy = \Delta(a)^{-1}\,\psi(\xi u)\,\int_{\mathbb{A}_F} f(z)\,\psi(-(\xi\, a^{-1} z))\,dz,$$
--   where $\Delta(a)$ denotes the value at $a$ of the distributive Haar character `distribHaarChar` of $\mathbb{A}_F$, a non-negative real scalar, regarded as a complex number and inverted, and $a^{-1}$ is the inverse idele acting by multiplication. Both integrals are Bochner integrals with respect to `adelicAddHaar`; for non-integrable integrands they vanish, and the identity then reads $0 = 0$.
--
--   This is the change-of-variables formula for the additive Haar measure of the adeles under the affine substitution $y \mapsto a(y+u)$: translation invariance contributes the character value $\psi(\xi u)$, and multiplication by the idele $a$ scales the measure by its module $\Delta(a)$. It is used in the computation of Whittaker coefficients and Weyl intertwining integrals of adelic Eisenstein series, being cited by the results on induced sections, on the meromorphic continuation of partial Euler products times intertwining integrals, and on the Euler-product form of Bruhat–Eisenstein Whittaker coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinGeneral_Piece_integral_smul_add_mul_addChar_neg_mul_eq.lean

import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem EisensteinGeneral.Piece.integral_smul_add_mul_addChar_neg_mul_eq (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (f : AdeleRing (𝓞 F) F → ℂ) (a : (AdeleRing (𝓞 F) F)ˣ)
    (u ξ : AdeleRing (𝓞 F) F) :
    ∫ y, f (a • (y + u)) * ψ (-(ξ * y)) ∂(adelicAddHaar (𝓞 F) F)
      = (((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) : ℂ)⁻¹ * ψ (ξ * u)
        * ∫ z, f z * ψ (-(ξ * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z)) ∂(adelicAddHaar (𝓞 F) F) := by sorry
