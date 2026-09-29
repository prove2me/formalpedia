-- Prove2me | Theorems.Thm_EisensteinGeneral_Glue_integrable_mul_of_integrable_of_integrable
-- name    : EisensteinGeneral.Glue.integrable_mul_of_integrable_of_integrable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/500b7ef7-c8ff-5bda-b96a-ea4c345f8eca
-- title:
--   Integrability of split functions on the adele ring
-- statement:
--   Let $F$ be a number field. The adele ring $\mathbb{A}_F$, realised as the product of the infinite adele ring and the finite adele ring of $\mathcal{O}_F \subset F$, is equipped with a measurable structure that is the Borel structure of its topology, and $\mu$ is an additive Haar measure on $\mathbb{A}_F$; likewise the finite adele ring is equipped with its Borel measurable structure and $\nu$ is an additive Haar measure on it. Let $f$ be a complex-valued function on the mixed space of $F$, i.e. on the product over the real places of copies of $\mathbb{R}$ and over the complex places of copies of $\mathbb{C}$, and let $g$ be a complex-valued function on the finite adele ring. Assume $f$ is integrable with respect to the canonical (Lebesgue) volume measure of the mixed space and $g$ is integrable with respect to $\nu$. The conclusion is that the function on $\mathbb{A}_F$ sending $x$ to $f(\iota(x_\infty)) \cdot g(x_{\mathrm{fin}})$, where $x_\infty$ and $x_{\mathrm{fin}}$ are the infinite and finite components of $x$ and $\iota$ is the ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace F` from the infinite adeles to the mixed space, is integrable with respect to $\mu$.
--
--   This is the integrability half of Fubini's theorem for the decomposition of the adeles into their archimedean and non-archimedean parts, stated so that it applies to an arbitrary Haar measure on $\mathbb{A}_F$ rather than only to a product measure; the passage from a product measure to a general Haar measure uses [`NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing`](thm.html#NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing), which says that any two additive Haar measures on $\mathbb{A}_F$ differ by a positive scalar. It serves as a basic integrability criterion for the adelic integrals occurring in the analytic theory of Eisenstein series and intertwining operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinGeneral_Glue_integrable_mul_of_integrable_of_integrable.lean

import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory NumberField IsDedekindDomain
set_option autoImplicit false

open scoped Classical in

theorem EisensteinGeneral.Glue.integrable_mul_of_integrable_of_integrable (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (f : mixedEmbedding.mixedSpace F → ℂ) (g : FiniteAdeleRing (𝓞 F) F → ℂ)
    (hf : Integrable f MeasureTheory.volume) (hg : Integrable g ν) :
    Integrable (fun x : AdeleRing (𝓞 F) F => f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * g x.2) μ := by sorry
