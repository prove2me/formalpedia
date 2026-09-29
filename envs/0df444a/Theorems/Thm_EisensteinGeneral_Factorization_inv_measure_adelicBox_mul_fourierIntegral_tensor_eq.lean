-- Prove2me | Theorems.Thm_EisensteinGeneral_Factorization_inv_measure_adelicBox_mul_fourierIntegral_tensor_eq
-- name    : EisensteinGeneral.Factorization.inv_measure_adelicBox_mul_fourierIntegral_tensor_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/2d6d62f8-9dec-551e-89c8-b7e39aced56d
-- title:
--   Box-normalised Fourier integral of a pure tensor factors
-- statement:
--   Let $F$ be a number field with ring of integers $\mathcal O_F$, discriminant $d_F$, and $\mathrm{nrComplexPlaces}\,F$ complex places. Equip the adele ring $\mathbb A_F=\mathbb A_{F,\infty}\times\mathbb A_{F,f}$ and the finite adele ring $\mathbb A_{F,f}$ with measurable structures that are Borel for their topologies, and let $\mu$, $\nu$ be additive Haar measures on them respectively. Let $\psi$ be an additive character of the additive group of $\mathbb A_F$ with values in $\mathbb C$ (no continuity assumed), let $f$ be any function on the mixed space $\mathbb R^{r_1}\times\mathbb C^{r_2}$ of $F$, let $g$ be any function on $\mathbb A_{F,f}$ (no integrability, measurability or decay assumed), and let $w=(w_\infty,w_f)\in\mathbb A_F$. Here the Fourier integral of a function $\phi$ on a ring $A$ against a character $\chi$, a measure $m$ and a point $u$ is the Bochner integral $\int_A \chi(-(v u))\,\phi(v)\,dm(v)$, which is $0$ when the integrand is not integrable. Write $B\subset\mathbb A_F$ for the adelic box, consisting of the adeles whose infinite component lies in the preimage, under the identification of $\mathbb A_{F,\infty}$ with the mixed space, of the fundamental domain of the lattice basis of $\mathcal O_F$, and whose finite component lies in $\prod_{v}\mathcal O_v$, the set of finite adeles integral at every height-one prime $v$ of $\mathcal O_F$. Then $\mu(B)^{-1}$ (as a real number, coerced to $\mathbb C$) times the Fourier integral against $\psi$, $\mu$ at $w$ of the pure tensor $x\mapsto f(x_\infty)g(x_f)$ equals $2^{\mathrm{nrComplexPlaces}\,F}/\sqrt{|d_F|}$ times the product of the Fourier integral of $f$ at $w_\infty$ against Lebesgue measure on the mixed space and the character obtained from $\psi$ by the inclusion of the infinite part (transported through the identification with the mixed space), with $\nu(\prod_v\mathcal O_v)^{-1}$ times the Fourier integral of $g$ at $w_f$ against $\nu$ and the character obtained from $\psi$ by the inclusion of the finite part.
--
--   This is the factorisation of an adelic Fourier transform of a pure tensor into its archimedean and finite parts, normalised by the measure of the adelic box so that the covolume $2^{-r_2}\sqrt{|d_F|}$ of $\mathcal O_F$ in the mixed space appears explicitly; it is the shape used when splitting adelic integrals in the manner of Tate's thesis. It is obtained from the corresponding factorisation of the unnormalised integral of a pure tensor, and is used in the computation of Whittaker coefficients and constant terms of Eisenstein series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinGeneral_Factorization_inv_measure_adelicBox_mul_fourierIntegral_tensor_eq.lean

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicFourier
import Mathlib.NumberTheory.NumberField.Discriminant.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox NumberField.AdelicFourier
  IsDedekindDomain

open scoped Classical in

theorem EisensteinGeneral.Factorization.inv_measure_adelicBox_mul_fourierIntegral_tensor_eq
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (f : mixedEmbedding.mixedSpace F → ℂ) (g : FiniteAdeleRing (𝓞 F) F → ℂ)
    (w : AdeleRing (𝓞 F) F) :
    ((μ (adelicBox F)).toReal : ℂ)⁻¹ *
        fourierIntegral ψ μ (fun x ↦ f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * g x.2) w
      = (((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
        * (fourierIntegral
              (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
                (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
              MeasureTheory.volume f (InfiniteAdeleRing.ringEquiv_mixedSpace F w.1)
          * (((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)⁻¹
              * fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr _ _)) ν g w.2)) := by sorry
