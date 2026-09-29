-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension
-- name    : AlgebraicCurve.Place.ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/28da6612-7502-5e70-9d2c-35fe64ed010d
-- title:
--   No cancellation of K'-weighted F-sums at lifted places
-- statement:
--   Let $K \subseteq K'$ and $F \subseteq F'$ be fields with $K \to F$, $K' \to F'$, $K \to K'$, $F \to F'$ and $K \to F'$ algebra structures forming compatible scalar towers $K \subseteq K' \subseteq F'$ and $K \subseteq F \subseteq F'$, with $K$ and $K'$ algebraically closed, and assume `IsCurveOver K F` and `IsCurveOver K' F'`: in each case every nonzero element has a degree-zero principal divisor recording its orders at all places, every place has residue field finite over the constant field, and the module of Kähler differentials is free of rank one over the function field. Assume further that $F$ is finite over $K(x)$ for some $x$ transcendental over $K$, that $F'$ is finite over $K'(x')$ for some $x'$ transcendental over $K'$, and that $F'$ is generated over $K'$ by the image of $F$. Here a place is a valuation subring of the function field containing the image of the constant field, distinct from the whole field and a principal ideal ring, and $\mathrm{ord}$ denotes minus the logarithm of the associated adic valuation. Let $\mathrm{lift}$ be any map from places of $F/K$ to places of $F'/K'$ satisfying $\mathrm{ord}_{\mathrm{lift}\,P}(f) = \mathrm{ord}_P(f)$ for all $f \in F$ and all $P$. Fix a place $v$ of $F/K$, a family $B : \iota \to K'$ that is linearly independent over $K$, and a nonzero finitely supported $g : \iota \to_0 F$. Then $\Sigma = \sum_{j \in \operatorname{supp} g} B_j\, g_j \in F'$ is nonzero, and $\mathrm{ord}_{\mathrm{lift}\,v}(\Sigma) \le \mathrm{ord}_v(g_j)$ for every $j \in \operatorname{supp} g$.
--
--   This is the no-cancellation half of the behaviour of places under a constant field extension, the computational core of the statement that the Riemann–Roch space of a divisor does not grow when the constant field is enlarged (Stichtenoth, Theorem 3.6.3(a)). It is used by [`AlgebraicCurve.mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain`](thm.html#AlgebraicCurve.mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain) to deduce membership of each coordinate $g_j$ in the Riemann–Roch space over $K$ from membership of the weighted sum over $K'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (lift : Place K F → Place K' F')
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (v : Place K F) {ι : Type*} (B : ι → K') (hB : LinearIndependent K B)
    (g : ι →₀ F) (hg : g ≠ 0) :
    (∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j)) ≠ 0 ∧
    ∀ j ∈ g.support,
      (lift v).ord (∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j)) ≤
        v.ord (g j) := by sorry
