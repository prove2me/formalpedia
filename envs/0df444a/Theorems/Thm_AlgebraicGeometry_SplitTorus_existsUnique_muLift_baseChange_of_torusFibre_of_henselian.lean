-- Prove2me | Theorems.Thm_AlgebraicGeometry_SplitTorus_existsUnique_muLift_baseChange_of_torusFibre_of_henselian
-- name    : AlgebraicGeometry.SplitTorus.existsUnique_muLift_baseChange_of_torusFibre_of_henselian
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/d3029e08-4e64-5ec6-bf73-902b6c4e3f55
-- title:
--   Lifting μ_m^t to a base change over a henselian ring
-- statement:
--   Let $R_0$ be a commutative ring, let $A$ be a henselian local ring whose residue field $\kappa =$ `ResidueField A` is algebraically closed, and let $\sigma \colon \operatorname{Spec} A \to \operatorname{Spec} R_0$ be any morphism. Let $g \colon G \to \operatorname{Spec} R_0$ be smooth, separated and quasi-compact, equipped with a relative group law $L$ — a group structure on the sections $\{\varphi \colon T \to G \mid \varphi \circ g = t\}$ for every $t \colon T \to \operatorname{Spec} R_0$, natural in $T$ — which is commutative. Let $m > 0$ be such that the morphism $[m] \colon G \to G$ obtained from $L$ by $m$-fold addition of the identity section is locally quasi-finite and flat. Let $t \in \mathbb{N}$ and let $\tau$ be a morphism $\operatorname{Spec}\kappa[\mathbb{Z}^t] \to G \times_{R_0} \kappa$ over $\kappa$, where the base change is along $\operatorname{Spec}\kappa \to \operatorname{Spec} A \to \operatorname{Spec} R_0$, such that $\tau$ is a closed immersion and is multiplicative on characters: for all $\chi, \chi'$ in the convolution monoid `WithConv` of $\kappa$-algebra maps $\kappa[\mathbb{Z}^t] \to \kappa$, the $\kappa$-point of $G\times_{R_0}\kappa$ obtained by precomposing $\tau$ with the point attached to $\chi\chi'$ is the product, under the base-changed law, of those attached to $\chi$ and $\chi'$. Then there is a morphism $\iota \colon \operatorname{Spec} A[(\mathbb{Z}/m)^t] \to G \times_{R_0,\sigma} A$ over $A$ which is a closed immersion, is multiplicative on points in the same sense for every $A$-algebra $S$ and all $\chi,\chi'$ in the convolution monoid of $A$-algebra maps $A[(\mathbb{Z}/m)^t] \to S$, and whose restriction over $\kappa$, read in $G$ through the first projection, agrees with $\tau$ restricted along $\operatorname{Spec}\kappa[(\mathbb{Z}/m)^t] \to \operatorname{Spec}\kappa[\mathbb{Z}^t]$; moreover any morphism $\iota'$ over $A$ satisfying these last two conditions (multiplicativity on points and the prescribed restriction over $\kappa$, with no closed-immersion requirement) equals $\iota$.
--
--   This is the base-changed form of the henselian lifting theorem for the toric part: a split torus in the closed fibre of a smooth commutative group scheme lifts uniquely to a multiplicative-type subgroup $\mu_m^t$ over the henselian base, here over $\operatorname{Spec} A$ mapping to $\operatorname{Spec} R_0$ through an arbitrary $\sigma$. It is used in the construction of the toric lifts inside the Néron objects attached to $J_0$ and $J_H$ at $p$, and in the analysis of the inertia and decomposition action on such a lift.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SplitTorus_existsUnique_muLift_baseChange_of_torusFibre_of_henselian.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SplitTorus IsLocalRing

theorem AlgebraicGeometry.SplitTorus.existsUnique_muLift_baseChange_of_torusFibre_of_henselian
    {R₀ : Type u} [CommRing R₀] {A : Type u} [CommRing A] [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (σ : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R₀))
    {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R₀)) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (L : RelativeGroupLaw R₀ g) (hcomm : L.IsCommutative)
    (m : ℕ) (hm : 0 < m) (hqf : LocallyQuasiFinite (L.schemeNsmul m)) (hfl : Flat (L.schemeNsmul m))
    (t : ℕ)
    (τ : SchemeHomOver (torusStr (ResidueField A) t)
      (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (residue A)) ≫ σ) g))
    (hτ : IsClosedImmersion τ.1)
    (hτmul : ∀ χ χ' : WithConv (torusCoord (ResidueField A) t →ₐ[ResidueField A] ResidueField A),
      NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField A) t (χ * χ').ofConv) τ =
        (L.baseChange (Spec.map (CommRingCat.ofHom (residue A)) ≫ σ)).mul _
          (NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField A) t χ.ofConv) τ)
          (NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField A) t χ'.ofConv) τ)) :
    ∃ ι : SchemeHomOver (muStr A t m) (RelativeGroupLaw.baseChangeStr σ g),
      (IsClosedImmersion ι.1 ∧
      (∀ (S : Type u) [CommRing S] [Algebra A S] (χ χ' : WithConv (muCoord A t m →ₐ[A] S)),
        NeronModelInfra.schemeHomOverComp (muPt A S t m (χ * χ').ofConv) ι =
          (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A S t m χ.ofConv) ι)
            (NeronModelInfra.schemeHomOverComp (muPt A S t m χ'.ofConv) ι)) ∧
      (muBaseChange (residue A) t m ≫ ι.1 ≫ pullback.fst g σ =
        muToTorus (ResidueField A) t m ≫ τ.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (residue A)) ≫ σ))) ∧
      ∀ ι' : SchemeHomOver (muStr A t m) (RelativeGroupLaw.baseChangeStr σ g),
        (∀ (S : Type u) [CommRing S] [Algebra A S] (χ χ' : WithConv (muCoord A t m →ₐ[A] S)),
          NeronModelInfra.schemeHomOverComp (muPt A S t m (χ * χ').ofConv) ι' =
            (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A S t m χ.ofConv) ι')
              (NeronModelInfra.schemeHomOverComp (muPt A S t m χ'.ofConv) ι')) →
        (muBaseChange (residue A) t m ≫ ι'.1 ≫ pullback.fst g σ =
          muToTorus (ResidueField A) t m ≫ τ.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (residue A)) ≫ σ)) →
        ι' = ι := by sorry
