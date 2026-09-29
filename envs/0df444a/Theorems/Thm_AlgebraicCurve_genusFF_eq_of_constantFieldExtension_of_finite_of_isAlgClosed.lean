-- Prove2me | Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed
-- name    : AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/00c133e9-b095-54db-92b3-a9c2a21228b0
-- title:
--   Genus invariance under constant-field extension in Frobenius form
-- statement:
--   Let $k$ be a finite field and $K$ an algebraically closed field, and let $F_0$, $F$ be fields equipped with algebra structures $k \to F_0$, $K \to F$ and $F_0 \to F$ (no compatibility between these three maps is assumed beyond what `hφ` below forces). Assume `IsCurveOver k F₀` and `IsCurveOver K F`: in each case every nonzero element has a degree-zero divisor recording its orders at all places, every place has residue field finite-dimensional over the base field, and the module of Kähler differentials is free of rank one over the function field; here a place of $F/K$ is a proper valuation subring of $F$ containing the image of $K$ which is a principal ideal ring, and a divisor is a finitely supported integer-valued function on places. Assume further that $F_0$ is generated over $k$ by a finite subset (`hfg`), that the image of $F_0$ in $F$ generates $F$ over $K$ (`hgen`), that there is a $K$-algebra endomorphism $\varphi$ of $F$ with $\varphi(x) = x^{\#k}$ for every $x$ in the image of $F_0$ (`hφ`), and that $L(0) \subseteq F_0$ is exactly the image of $k$ in $F_0$ (`hC`). Then $\operatorname{genusFF} K F = \operatorname{genusFF} k F_0$, where the genus of $E/L$ is the $L$-dimension of $H^1$ at the zero divisor.
--
--   This is the classical invariance of the genus of a one-variable function field under extension of the constant field, here from a finite field $k$ to an algebraically closed field $K$, with the extension presented through a relative $\#k$-power Frobenius endomorphism of $F$ rather than through a tower of algebra maps. It feeds the comparison of the places of $F_0/k$ with the Frobenius-fixed places of $F/K$, and is cited by [`AlgebraicCurve.exists_monic_natCard_fixedPoints_restrictAlong_eq_of_constantFieldExtension`](thm.html#AlgebraicCurve.exists_monic_natCard_fixedPoints_restrictAlong_eq_of_constantFieldExtension).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (hC : AlgebraicCurve.ConstantsAreBase k F₀) :
    AlgebraicCurve.genusFF K F = AlgebraicCurve.genusFF k F₀ := by sorry
