-- Prove2me | Theorems.Thm_Algebra_isUnramifiedAt_iff_map_maximalIdeal_eq_and_isSeparable_of_height_eq_one
-- name    : Algebra.isUnramifiedAt_iff_map_maximalIdeal_eq_and_isSeparable_of_height_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/de747e8f-7315-562f-9d07-2b2edd630887
-- title:
--   Unramifiedness at a height-one prime: DVR criterion
-- statement:
--   Let $O$ and $C$ be commutative rings that are Noetherian integrally closed domains, with $C$ an $O$-algebra that is module-finite over $O$ and has no zero smul-divisors (so the structure map $O \to C$ is injective and $C$ is torsion-free over $O$). Let $P$ be a prime ideal of $C$ of height $1$, write $P \cap O$ for the contracted prime `P.under O`, and assume given an algebra structure of the localisation $O_{P \cap O}$ on the localisation $C_P$ which is compatible with the lying-over data, i.e. satisfies Mathlib's `Localization.AtPrime.IsLiesOverAlgebra`. The conclusion is a fourfold conjunction: (i) $P \cap O$ also has height $1$; (ii) $O_{P\cap O}$ is a discrete valuation ring; (iii) $C_P$ is a discrete valuation ring; and (iv) $C$ is unramified over $O$ at $P$ in the sense of `Algebra.IsUnramifiedAt` if and only if both the ideal generated in $C_P$ by the image of $P \cap O$ under $O \to C_P$ equals the maximal ideal of $C_P$, and the residue field extension $\kappa(P)/\kappa(P \cap O)$ is separable.
--
--   This is the standard translation, for a module-finite extension of normal Noetherian domains, between unramifiedness at a height-one prime and the valuation-theoretic conditions "the base uniformiser remains a uniformiser" together with separability of the residue extension. It is used in the analysis of models of modular curves, where ramification at height-one primes of explicit charts is checked by exhibiting uniformisers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_isUnramifiedAt_iff_map_maximalIdeal_eq_and_isSeparable_of_height_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Algebra.isUnramifiedAt_iff_map_maximalIdeal_eq_and_isSeparable_of_height_eq_one
    {O C : Type*} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
    [CommRing C] [IsDomain C] [IsNoetherianRing C] [IsIntegrallyClosed C]
    [Algebra O C] [Module.Finite O C] [NoZeroSMulDivisors O C]
    (P : Ideal C) [P.IsPrime] (hP : P.height = 1)
    [Algebra (Localization.AtPrime (P.under O)) (Localization.AtPrime P)]
    [Localization.AtPrime.IsLiesOverAlgebra (P.under O) P] :
    (P.under O).height = 1 ∧
    IsDiscreteValuationRing (Localization.AtPrime (P.under O)) ∧
    IsDiscreteValuationRing (Localization.AtPrime P) ∧
    (Algebra.IsUnramifiedAt O P ↔
      Ideal.map (algebraMap O (Localization.AtPrime P)) (P.under O) =
          IsLocalRing.maximalIdeal (Localization.AtPrime P) ∧
      Algebra.IsSeparable (P.under O).ResidueField P.ResidueField) := by sorry
