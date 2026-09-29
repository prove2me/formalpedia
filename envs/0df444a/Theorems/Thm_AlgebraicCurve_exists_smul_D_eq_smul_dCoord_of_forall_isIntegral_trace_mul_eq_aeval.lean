-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_smul_D_eq_smul_dCoord_of_forall_isIntegral_trace_mul_eq_aeval
-- name    : AlgebraicCurve.exists_smul_D_eq_smul_dCoord_of_forall_isIntegral_trace_mul_eq_aeval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/f30346ff-b035-5d9f-ac52-7cf09fc1e635
-- title:
--   Dedekind: x dt is regular where t is finite
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field extension of $K$ satisfying [`AlgebraicCurve.IsCurveOver K F`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero $f \in F$ admits a divisor of degree $0$ whose multiplicity at each place $v$ is $\operatorname{ord}_v f$, every place of $F$ over $K$ has residue field finite-dimensional over $K$, and $\Omega_{F/K}$ is free of rank one over $F$. Here a place is a valuation subring of $F$ other than $F$ itself which contains the image of $K$ and is a principal ideal ring, and $\operatorname{ord}_v$ is minus the logarithm of its associated adic valuation. Let $t \in F$ be transcendental over $K$ and suppose $F$ is finite-dimensional over the intermediate field $K(t) =$ `IntermediateField.adjoin K {t}`. Let $x \in F$ be such that for every $b \in F$ integral over the subalgebra $K[t] =$ `Algebra.adjoin K {t}`, the trace $\operatorname{Tr}_{F/K(t)}(xb)$, viewed inside $F$, equals $P(t)$ for some polynomial $P$ over $K$. Then for every place $w$ of $F$ over $K$ with $\operatorname{ord}_w t \ge 0$ there is an element $g$ of the valuation subring of $w$ with $x \cdot \mathrm{d}t = g \cdot \mathrm{d}\pi_w$ in $\Omega_{F/K}$, where $\pi_w$ is the uniformiser of $w$ chosen in the definition of [`AlgebraicCurve.Place.dCoord`](def/ModularCurve_CanonicalDivisor.html#L30).
--
--   This is one half of Dedekind's theorem relating the different of the integral closure of $K[t]$ in $F$ to the module of differentials, in the geometric form asserting that an element of the complementary module of $K[t]$ in $F$ yields a differential $x\,\mathrm{d}t$ regular at every place where $t$ is finite. It is used in the construction of regular differentials on modular curves, via the statements about $q$-expansions of regular differentials and about $\mathrm{d}j$ that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_smul_D_eq_smul_dCoord_of_forall_isIntegral_trace_mul_eq_aeval.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.exists_smul_D_eq_smul_dCoord_of_forall_isIntegral_trace_mul_eq_aeval
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [AlgebraicCurve.IsCurveOver K F]
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
    (x : F)
    (hx : ∀ b : F, IsIntegral (Algebra.adjoin K ({t} : Set F)) b →
      ∃ P : Polynomial K,
        ((Algebra.trace (IntermediateField.adjoin K ({t} : Set F)) F (x * b) :
            IntermediateField.adjoin K ({t} : Set F)) : F) = Polynomial.aeval t P)
    (w : AlgebraicCurve.Place K F) (hw : 0 ≤ w.ord t) :
    ∃ g ∈ w.toValuationSubring, x • KaehlerDifferential.D K F t = g • w.dCoord := by sorry
