-- Prove2me | Theorems.Thm_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring
-- name    : FixedPoints.faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/394fb95c-d788-5f30-a30a-b3a4dcad8762
-- title:
--   Quotient group inherits the frame on the fixed subring
-- statement:
--   Let $R$ be a discrete valuation ring which is a domain, and let $G$ be a finite group acting on $R$ by ring automorphisms, the action being faithful. Assume that the maximal ideal of $R$ lies over the maximal ideal of the fixed subring $R^{G}$ (i.e. it contracts to it along the inclusion), that the residue extension $R^{G}/\mathfrak m_{R^{G}} \to R/\mathfrak m_{R}$ is separable, and that the residue field of $R$ is perfect. Let $H \le G$ be a normal subgroup. Then three assertions hold for the fixed subring $R^{H}$, equipped with the induced action of $G/H$: the action of $G/H$ on $R^{H}$ is faithful; the residue field of $R^{H}$ is perfect; and the maximal ideal of $R^{H}$ lies over the maximal ideal of $(R^{H})^{G/H}$, with the associated residue extension $(R^{H})^{G/H}/\mathfrak m \to R^{H}/\mathfrak m_{R^{H}}$ separable (the last two being packaged as an existential statement, the lying-over datum followed by separability over it).
--
--   This is the descent step which shows that the hypotheses under which the ramification theory of a finite group acting on a discrete valuation ring is developed — faithfulness, lying over of the maximal ideal above the fixed subring, separability of the residue extension, and perfectness of the residue field — are inherited by $R^{H}$ with its $G/H$-action, for $H$ normal in $G$. It is used in the inductive arguments on ramification groups, Herbrand-type comparisons and the Hasse–Arf chain for commutative actions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Definitions.Def_RamificationChain_Wild

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem FixedPoints.faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    [PerfectField (IsLocalRing.ResidueField R)]
    (H : Subgroup G) [H.Normal] :
    FaithfulSMul (G ⧸ H) (FixedPoints.subring R H) ∧
    PerfectField (IsLocalRing.ResidueField (FixedPoints.subring R H)) ∧
    ∃ (_ : (IsLocalRing.maximalIdeal (FixedPoints.subring R H)).LiesOver
      (IsLocalRing.maximalIdeal (FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H)))),
      Algebra.IsSeparable
        (FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H) ⧸
          IsLocalRing.maximalIdeal (FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H)))
        (FixedPoints.subring R H ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R H)) := by sorry
