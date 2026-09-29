-- Prove2me | Theorems.Thm_CerednikDrinfeld_ShimuraCurveModel_galJ_eq_self_of_mem_inertiaSubgroupIn_of_smoothOfRelativeDimension_one
-- name    : CerednikDrinfeld.ShimuraCurveModel.galJ_eq_self_of_mem_inertiaSubgroupIn_of_smoothOfRelativeDimension_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/472739d9-dc05-574e-b772-561dedc7d2d7
-- title:
--   Inertia fixes p-torsion of a Shimura curve Jacobian
-- statement:
--   Fix $a,b\in\mathbb Q$, a $\mathbb Z$-submodule $R$ of $\mathbb H[\mathbb Q,a,b]$, a $\mathbb Q$-algebra map $\iota$ of that quaternion algebra into $M_2(\mathbb R)$, a family $\mathcal S$ of sets of units of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb A_{\mathbb Q}^{f}$, and a Shimura curve model $M$ for these data, with its function fields $M.F/\mathbb Q$, $M.\overline{F}/\overline{\mathbb Q}$, its semilinear Galois action $M.\mathrm{gal}$ and the group $M.J$ it acts on. Let $O$ be a discrete valuation domain with an injective ring map $i:O\to\overline{\mathbb Q}$; let $c:C\to\operatorname{Spec}O$ be proper, smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a section of $c$ (a morphism $\operatorname{Spec}O\to C$ whose composite with $c$ is the identity). Let $\mathfrak M$ be a curve model of $M.\overline{F}$ over $\overline{\mathbb Q}$ — an integral scheme, proper and smooth of relative dimension one over $\operatorname{Spec}\overline{\mathbb Q}$, with function field identified with $M.\overline{F}$ and closed points in bijection with the places of $M.\overline{F}/\overline{\mathbb Q}$ — together with an isomorphism $e:\mathfrak M.C\to C\times_{\operatorname{Spec}O}\operatorname{Spec}\overline{\mathbb Q}$ whose composite with the second projection is $\mathfrak M.\mathrm{toBase}$. Assume equivariance: for every $\sigma\in\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ fixing $i(O)$ pointwise and all $\overline{\mathbb Q}$-points $x,y$ of $\mathfrak M.C$ over the base, if the first-projection image of $y$ equals $\operatorname{Spec}(\sigma)$ followed by that of $x$, then the place attached to $y$ by $\mathfrak M.\mathrm{pointEquivPlace}$ is $M.\mathrm{gal}\,\sigma$ applied to the place attached to $x$. Let $B$ be a valuation subring of $\overline{\mathbb Q}$ containing $i(O)$ and such that every element of $B.\mathrm{inertiaSubgroupIn}\ \mathbb Q$ (the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $B$) fixes $i(O)$ pointwise, and let $p$ be a natural number whose image in $O$ is a unit. Then for every $\sigma$ in that inertia subgroup and every $t\in M.J$ with $p\cdot t=0$ one has $M.\mathrm{galJ}\,\sigma\,t=t$, where $M.\mathrm{galJ}\,\sigma$ is the additive automorphism of $M.J$ given by the action of the semilinear automorphism $M.\mathrm{gal}\,\sigma$.
--
--   This is the elementary direction of the Néron–Ogg–Shafarevich criterion (Serre–Tate) in the form needed for Shimura curves: a smooth proper model over a discrete valuation ring in which $p$ is invertible forces inertia at the corresponding place to act trivially on the $p$-torsion of the Jacobian. It is the form in which the unramified clause of the good-reduction condition `GoodReductionOutside` for a Shimura curve model is discharged, and it is used by the variant phrased in terms of a moduli witness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_ShimuraCurveModel_galJ_eq_self_of_mem_inertiaSubgroupIn_of_smoothOfRelativeDimension_one.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian AlgebraicCurve IsDedekindDomain QuaternionAlgebra CerednikDrinfeld
open AlgebraicGeometry

theorem CerednikDrinfeld.ShimuraCurveModel.galJ_eq_self_of_mem_inertiaSubgroupIn_of_smoothOfRelativeDimension_one
    {a b : ℚ} {R : Submodule ℤ ℍ[ℚ, a, b]} {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (M : ShimuraCurveModel R ι 𝒮)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (i : O →+* AlgebraicClosure ℚ) (hi : Function.Injective i)

    {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of O)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) c)

    (𝔐 : CurveModel (AlgebraicClosure ℚ) M.Fbar)
    (e : 𝔐.C ⟶ pullback c (Spec.map (CommRingCat.ofHom i))) [IsIso e]
    (he : e ≫ pullback.snd c (Spec.map (CommRingCat.ofHom i)) = 𝔐.toBase)

    (hgal : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ r : O, σ (i r) = i r) →
      ∀ x y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔐.C // q ≫ 𝔐.toBase = 𝟙 _},
        y.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
            x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) →
        𝔐.pointEquivPlace y = M.gal σ • 𝔐.pointEquivPlace x)

    (B : ValuationSubring (AlgebraicClosure ℚ)) (hB : ∀ r : O, i r ∈ B)
    (hfix : ∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ r : O, σ (i r) = i r)
    (p : ℕ) (hp : IsUnit ((p : ℕ) : O)) :
    ∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ t : M.J, p • t = 0 → M.galJ σ t = t := by sorry
