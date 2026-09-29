-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_derivation_constantFieldExtension_map_mem
-- name    : AlgebraicCurve.exists_derivation_constantFieldExtension_map_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/11ccb33e-8507-5246-9ff0-97b5f0d818a2
-- title:
--   Horizontal lift of a constant derivation to a constant field extension
-- statement:
--   Let $K$, $F$, $E$, $FE$ be fields with $K$-algebra structures on $F$ and $E$, an $E$-algebra and an $F$-algebra structure on $FE$, and a $K$-algebra structure on $FE$ making both towers $K \to E \to FE$ and $K \to F \to FE$ compatible; assume $K$ is algebraically closed of characteristic $0$ and $E$ is algebraically closed. Assume $F$ contains an element transcendental over $K$ over whose generated intermediate field $F$ is finite, and likewise $FE$ contains an element transcendental over $E$ over whose generated intermediate field $FE$ is finite. Assume further that $F/K$ and $FE/E$ each satisfy `IsCurveOver`, i.e.\ every nonzero element has an associated degree-zero divisor recording its order at every place, every place has residue field finite over the base field, and the module of Kähler differentials is free of rank $1$ over the function field; here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$ itself, and a principal ideal ring. Assume finally that $FE$ is generated over $E$ by the image of $F$, and let $\delta$ be a $K$-derivation of $E$. Then there exists a $K$-derivation $D$ of $FE$ that vanishes on the image of $F$, restricts along $E \to FE$ to $\delta$, and maps each valuation subring attached to a place of $FE/E$ into itself.
--
--   This is the horizontal lift of a derivation of the constant field to a constant field extension $FE = E\cdot F$ of a one-variable function field: the derivation $1 \otimes \delta$ acting trivially on $F$, together with the statement that the resulting vector field is regular at every place of $FE/E$. It is used in the comparison of differentials and divisors under constant field extension, in particular for the vanishing of the sum of orders of a pulled-back differential and for descent of torsion divisor classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_derivation_constantFieldExtension_map_mem.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.exists_derivation_constantFieldExtension_map_mem
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE]
    [Algebra K F] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (δ : Derivation K E E) :
    ∃ D : Derivation K FE FE,
      (∀ f : F, D (algebraMap F FE f) = 0) ∧
      (∀ e : E, D (algebraMap E FE e) = algebraMap E FE (δ e)) ∧
      ∀ (P : Place E FE) (z : FE), z ∈ P.toValuationSubring → D z ∈ P.toValuationSubring := by sorry
