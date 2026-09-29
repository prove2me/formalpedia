-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_residue_integralClosure_surjective_of_genusFF_eq
-- name    : AlgebraicCurve.RegularProlongation.residue_integralClosure_surjective_of_genusFF_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/a0ac5a66-5a4d-5662-9f34-60d7e04bf7dd
-- title:
--   Equal genera force surjective reduction onto affine charts
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring with residue field $k =$ `IsLocalRing.ResidueField A`, let $F$ be a field extension of $L$ and $\bar F$ a field extension of $k$, each of which is a curve in the sense of `IsCurveOver` over its base (principal divisors of degree zero for every nonzero function, residue fields of all places finite over the base, and module of Kähler differentials free of rank one). Let $R$ be a regular prolongation of $A$ to $F$ with reduction $\bar F$: a valuation subring $\mathcal O = R.integers$ of $F$ together with a surjective ring homomorphism $\mathrm{res} \colon \mathcal O \to \bar F$ whose kernel is the maximal ideal of $\mathcal O$, such that $a \in L$ lies in $\mathcal O$ exactly when $a \in A$, $\mathrm{res}$ is compatible with $A \to k$, and every nonzero $f \in F$ admits $c \in L$ with $cf \in \mathcal O$ and $\mathrm{res}(cf) \neq 0$. Let $x \in \mathcal O$ be such that $\bar x = \mathrm{res}(x)$ is transcendental over $k$, such that $\mathrm{finrank}_{k(\bar x)} \bar F > 0$ (so $\bar F$ is finite over $k(\bar x)$), and such that $[F : L(x)] = [\bar F : k(\bar x)]$; assume moreover that the genera agree, $\mathrm{genusFF}(k, \bar F) = \mathrm{genusFF}(L, F)$, where $\mathrm{genusFF}(K, F) = \mathrm{finrank}_K H^1(0)$ for the zero divisor. The conclusion is twofold: every $h \in \bar F$ integral over $k[\bar x]$ is $\mathrm{res}(f)$ for some $f \in \mathcal O$ integral over $L[x]$, and every $h \in \bar F$ integral over $k[\bar x^{-1}]$ is $\mathrm{res}(f)$ for some $f \in \mathcal O$ integral over $L[x^{-1}]$.
--
--   This is the surjectivity statement in Deuring's theory of reduction of algebraic function fields: under good reduction, recognised here by equality of the genera of $F/L$ and $\bar F/k$, the reduction map carries the ring of functions of $F$ regular away from the poles of $x$ onto the integral closure of $k[\bar x]$ in $\bar F$, and likewise for the chart at $x^{-1}$. It is used in the construction of good constant reductions with prescribed behaviour of places, and, downstream, in lifting the $j$-chart of characteristic-$p$ models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_residue_integralClosure_surjective_of_genusFF_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.residue_integralClosure_surjective_of_genusFF_eq
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [IsCurveOver (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hgood : genusFF (IsLocalRing.ResidueField A) Fbar = genusFF L F) :
    (∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h) ∧
    (∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {(R.residue x)⁻¹}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)⁻¹}) (f : F) ∧ R.residue f = h) := by sorry
