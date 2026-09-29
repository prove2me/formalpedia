-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_SchrodingerFrame_exists_sigma_eq_baseScalar_smul_of_isUnit
-- name    : AlgebraicGeometry.Polarisation.SchrodingerFrame.exists_sigma_eq_baseScalar_smul_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/dcaef83b-207d-5bc9-954c-a7bad32399cd
-- title:
--   Rescaling a Schrödinger frame by a base unit
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, $f : A \to \operatorname{Spec} S$ a morphism, and $L$ a relative group law on $f$, i.e. a functorial group structure (multiplication, unit, inverse, with associativity, unit and inverse laws, and naturality under base change of the test scheme) on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points of $A$ over $\operatorname{Spec} S$. Let $\mathcal{L}$ be an object of `A.Modules`, let $R$ be a commutative ring, $t : \operatorname{Spec} R \to \operatorname{Spec} S$, let $g : \mathbb{N}$ and $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with every $\delta(i)$ nonzero, and write $H = \prod_i \mathbb{Z}/\delta(i)$. Let $F$ be a Schrödinger frame of type $\delta$ for $\mathcal{L}$ over $t$: a family $\sigma : H \to \Gamma(\mathcal{L}|_{A \times_{\operatorname{Spec} S} \operatorname{Spec} R}, \top)$ (pullback along `pullback.fst f t`) such that $c \mapsto \sum_{h} \mathrm{baseScalar}\,f\,t\,(c\,h) \cdot \sigma(h)$ is a bijection from $H \to R$ onto those sections, together with theta points $\mathrm{lift}(h)$ and $\mathrm{dualLift}(\chi)$ (for $\chi$ an additive character $H \to R^\times$) whose actions satisfy $\mathrm{lift}(h).\mathrm{act}(\sigma(h')) = \sigma(h+h')$ and $\mathrm{dualLift}(\chi).\mathrm{act}(\sigma(h)) = \mathrm{baseScalar}\,f\,t\,(\chi(h)) \cdot \sigma(h)$; here $\mathrm{baseScalar}\,f\,t\,r$ is the global section of the fibre product obtained by pulling $r$ back along `pullback.snd f t`. Let $c \in R$ be a unit. Then there is a Schrödinger frame $F'$ of the same type with $F'.\sigma(h) = \mathrm{baseScalar}\,f\,t\,(c) \cdot F.\sigma(h)$ for every $h$, and with the same lifts and dual lifts: $F'.\mathrm{lift} = F.\mathrm{lift}$ and $F'.\mathrm{dualLift} = F.\mathrm{dualLift}$.
--
--   This is the statement that a Schrödinger-type basis of theta sections is determined only up to a global unit of the base ring, the attached theta points (the lifts of translations and the dual characters) being unchanged. It is used in the verification that a framed polarised abelian scheme is theta-adapted, where a given frame must be normalised by a unit without disturbing the theta group action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_SchrodingerFrame_exists_sigma_eq_baseScalar_smul_of_isUnit.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

universe u

theorem AlgebraicGeometry.Polarisation.SchrodingerFrame.exists_sigma_eq_baseScalar_smul_of_isUnit
    {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {L : RelativeGroupLaw S f}
    {𝓛 : A.Modules} {R : Type u} [CommRing R] {t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)}
    {g : ℕ} {δ : Fin g → ℕ} [hδ : ∀ i, NeZero (δ i)]
    (F : Polarisation.SchrodingerFrame f L 𝓛 t δ) (c : R) (hc : IsUnit c) :
    ∃ F' : Polarisation.SchrodingerFrame f L 𝓛 t δ,
      (∀ h, F'.σ h = Polarisation.baseScalar f t c • F.σ h) ∧ F'.lift = F.lift ∧ F'.dualLift = F.dualLift := by sorry
