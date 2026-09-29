-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_SchrodingerFrame_act_ofScalar_mul_lift_mul_dualLift_sigma
-- name    : AlgebraicGeometry.Polarisation.SchrodingerFrame.act_ofScalar_mul_lift_mul_dualLift_sigma
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/dd63235a-5cf7-5dfa-9268-8ff2cde8c320
-- title:
--   Schrödinger action of ωᵃθ_hη_χ on a frame
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme with a morphism $f : A \to \operatorname{Spec} S$, $L$ a relative group law on $f$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} S$, compatible with base change), and $\mathcal{L}$ a module on $A$. Let $R$ be a commutative ring and $t : \operatorname{Spec} R \to \operatorname{Spec} S$. Fix $g$, a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with all $\delta_i$ nonzero, a nonzero $d$, and $\omega \in R$ with $\omega^{2d} = 1$. Let $F$ be a Schrödinger frame of type $\delta$ for $(f, L, \mathcal{L}, t)$: a family $\sigma_h$ of global sections of the pullback of $\mathcal{L}$ along $\mathrm{pr}_1 : A \times_{\operatorname{Spec} S} \operatorname{Spec} R \to A$, indexed by $H(\delta) = \prod_i \mathbb{Z}/\delta_i$, such that $c \mapsto \sum_h \mathrm{baseScalar}(c_h)\,\sigma_h$ is a bijection from $R$-valued functions on $H(\delta)$ onto those sections, together with theta points $\mathrm{lift}(h)$ and $\mathrm{dualLift}(\chi)$ satisfying $\mathrm{lift}(h).\mathrm{act}(\sigma_{h'}) = \sigma_{h+h'}$ and $\mathrm{dualLift}(\chi).\mathrm{act}(\sigma_h) = \mathrm{baseScalar}(\chi(h)) \cdot \sigma_h$; here a theta point is a pair consisting of a point $x$ over $t$ and an isomorphism between the pullback of $\mathrm{pr}_1^{*}\mathcal{L}$ along translation by $x$ and $\mathrm{pr}_1^{*}\mathcal{L}$, acting on global sections by pulling back and applying that isomorphism, and $\mathrm{baseScalar}(r)$ denotes the image of $r \in R$ in $\Gamma(A \times_{\operatorname{Spec} S} \operatorname{Spec} R, \top)$ obtained from $\Gamma \circ \operatorname{Spec}$ and the second projection. Let $z = (a, h, k)$ be an element of $\mathrm{Heis}_{\delta,d}$, i.e. $a \in \mathbb{Z}/2d$ and $h, k \in H(\delta)$, let $\chi$ be an additive character $H(\delta) \to R$ with $\chi(y) = \omega^{\langle k, y\rangle}$ for all $y$, where $\langle k, y \rangle = \mathrm{pair}_{\delta,d}(k,y) \in \mathbb{Z}/2d$ and $\omega^{(\cdot)}$ means $\omega$ raised to the canonical representative, and let $c \in R^{\times}$ with $c = \omega^{a}$ in $R$. Then for every $y \in H(\delta)$, the theta point $\mathrm{ofScalar}(c) \cdot \mathrm{lift}(h) \cdot \mathrm{dualLift}(\chi)$ (product in the group of theta points, $\mathrm{ofScalar}(c)$ being the unit $c$ transported to $\Gamma$ of the fibre product) acts on $\sigma_y$ by $\mathrm{baseScalar}\big(\omega^{\,a + \langle k, y\rangle}\big) \cdot \sigma_{y + h}$.
--
--   This is the Schrödinger representation in normal form: an element of the theta group written as $\omega^{a}\theta_h\eta_\chi$ permutes the frame sections $\sigma_y$ up to the root-of-unity scalars $\omega^{a+\langle k,y\rangle}$, so that its matrix in the frame is the explicit Heisenberg matrix attached to $z$. It is used in the construction of theta-adapted frames and reframings for polarised abelian schemes, in particular by the statements producing idempotents and units compatible with a Schrödinger frame.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_SchrodingerFrame_act_ofScalar_mul_lift_mul_dualLift_sigma.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.Polarisation.SchrodingerFrame.act_ofScalar_mul_lift_mul_dualLift_sigma
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f) (𝓛 : A.Modules)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (ω : R) (hω : ω ^ (2 * d) = 1)
    (F : SchrodingerFrame f L 𝓛 t δ) (z : ThetaLevel.Heis δ d)
    (χ : AddChar (ThetaLevel.HH δ) R) (hχ : ∀ y, χ y = ThetaLevel.thetaChar δ d R ω z.k y)
    (c : Rˣ) (hc : (c : R) = ThetaLevel.omegaPow d R ω z.a) (y : ThetaLevel.HH δ) :
    (ThetaPt.ofScalar c * F.lift z.h * F.dualLift χ).act (F.σ y) =
      baseScalar f t (ThetaLevel.omegaPow d R ω (z.a + ThetaLevel.pair δ d z.k y)) • F.σ (y + z.h) := by sorry
