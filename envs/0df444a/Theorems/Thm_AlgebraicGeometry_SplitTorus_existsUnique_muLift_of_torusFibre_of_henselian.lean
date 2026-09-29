-- Prove2me | Theorems.Thm_AlgebraicGeometry_SplitTorus_existsUnique_muLift_of_torusFibre_of_henselian
-- name    : AlgebraicGeometry.SplitTorus.existsUnique_muLift_of_torusFibre_of_henselian
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/6855255d-c264-52b6-8d4d-e860ed627a19
-- title:
--   Unique lifting of μ_m^t from a split torus in the special fibre
-- statement:
--   Let $R$ be a henselian local ring whose residue field $\kappa =$ `ResidueField R` is algebraically closed, and let $g : G \to \operatorname{Spec} R$ be smooth, separated and quasi-compact. Let $L$ be a `RelativeGroupLaw` for $g$, that is, a group structure on the sections $\{\varphi : T \to G \mid \varphi \circ g = t\}$ for every $t : T \to \operatorname{Spec} R$, natural in $T$, and assume $L$ is commutative. Fix $t \in \mathbb{N}$ and a morphism $\tau$ from the split torus $\operatorname{Spec}\kappa[\mathbb{Z}^t] \to \operatorname{Spec}\kappa$ to the base change of $g$ along $\operatorname{Spec}\kappa \to \operatorname{Spec} R$, compatible with the two structure maps, such that $\tau$ is a closed immersion and is multiplicative on $\kappa$-points: for all $\chi,\chi'$ in the convolution monoid of $\kappa$-algebra maps $\kappa[\mathbb{Z}^t] \to \kappa$, the point $\tau \circ (\chi\chi')$ is the product, for the base-changed group law, of $\tau \circ \chi$ and $\tau \circ \chi'$. Let $m > 0$ be such that the endomorphism `L.schemeNsmul m` of $G$ (multiplication by $m$) is locally quasi-finite and flat. Then there is a morphism $\iota : \operatorname{Spec} R[(\mathbb{Z}/m)^t] \to G$ over $\operatorname{Spec} R$ which is a closed immersion, is multiplicative on $S$-points for every commutative $R$-algebra $S$ (in the same convolution sense, for $L$), and whose reduction along $R \to \kappa$ equals $\mu_{m,\kappa}^t \hookrightarrow \mathbb{G}_{m,\kappa}^t \xrightarrow{\tau} G_\kappa \to G$; moreover any morphism $\iota'$ over $\operatorname{Spec} R$ that is multiplicative on $S$-points for all $S$ and has that same reduction equals $\iota$ — uniqueness is asserted without assuming $\iota'$ a closed immersion.
--
--   This is the rigidity and lifting theorem for finite subgroups of multiplicative type over a henselian base, in the form used to build the toric part of the identity component of a Néron model: the $m$-torsion of a split torus in the special fibre lifts uniquely to a multiplicative closed subgroup scheme over $R$. It is used by the variant of the statement after base change of the group law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SplitTorus_existsUnique_muLift_of_torusFibre_of_henselian.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SplitTorus IsLocalRing

theorem AlgebraicGeometry.SplitTorus.existsUnique_muLift_of_torusFibre_of_henselian
    {R : Type u} [CommRing R] [HenselianLocalRing R] [IsAlgClosed (ResidueField R)]
    {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R)) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (L : RelativeGroupLaw R g) (hcomm : L.IsCommutative)
    (t : ℕ)
    (τ : SchemeHomOver (torusStr (ResidueField R) t)
      (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (residue R))) g))
    (hτ : IsClosedImmersion τ.1)
    (hτmul : ∀ χ χ' : WithConv (torusCoord (ResidueField R) t →ₐ[ResidueField R] ResidueField R),
      NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField R) t (χ * χ').ofConv) τ =
        (L.baseChange (Spec.map (CommRingCat.ofHom (residue R)))).mul _
          (NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField R) t χ.ofConv) τ)
          (NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField R) t χ'.ofConv) τ))
    (m : ℕ) (hm : 0 < m) (hqf : LocallyQuasiFinite (L.schemeNsmul m)) (hfl : Flat (L.schemeNsmul m)) :
    ∃ ι : SchemeHomOver (muStr R t m) g,
      (IsClosedImmersion ι.1 ∧
      (∀ (S : Type u) [CommRing S] [Algebra R S] (χ χ' : WithConv (muCoord R t m →ₐ[R] S)),
        NeronModelInfra.schemeHomOverComp (muPt R S t m (χ * χ').ofConv) ι =
          L.mul _ (NeronModelInfra.schemeHomOverComp (muPt R S t m χ.ofConv) ι)
            (NeronModelInfra.schemeHomOverComp (muPt R S t m χ'.ofConv) ι)) ∧
      (muBaseChange (residue R) t m ≫ ι.1 =
        muToTorus (ResidueField R) t m ≫ τ.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (residue R))))) ∧
      ∀ ι' : SchemeHomOver (muStr R t m) g,
        (∀ (S : Type u) [CommRing S] [Algebra R S] (χ χ' : WithConv (muCoord R t m →ₐ[R] S)),
        NeronModelInfra.schemeHomOverComp (muPt R S t m (χ * χ').ofConv) ι' =
          L.mul _ (NeronModelInfra.schemeHomOverComp (muPt R S t m χ.ofConv) ι')
            (NeronModelInfra.schemeHomOverComp (muPt R S t m χ'.ofConv) ι')) →
        (muBaseChange (residue R) t m ≫ ι'.1 =
        muToTorus (ResidueField R) t m ≫ τ.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (residue R)))) →
        ι' = ι := by sorry
