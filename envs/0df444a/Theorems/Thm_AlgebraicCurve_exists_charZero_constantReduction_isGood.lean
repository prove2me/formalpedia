-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_charZero_constantReduction_isGood
-- name    : AlgebraicCurve.exists_charZero_constantReduction_isGood
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/00a57568-69b7-587c-a973-88d1e21c0bb5
-- title:
--   Lifting a function field to a good constant reduction in characteristic zero
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field equipped with a $K$-algebra structure such that some $x \in F$ is transcendental over $K$ with $F$ finite-dimensional over the intermediate field $K(x)$, i.e. $F/K$ is a one-variable function field. The assertion is that there exist an algebraically closed field $L$ of characteristic zero (in the universe of $K$), a valuation subring $A \subseteq L$, a ring isomorphism $e$ from the residue field of $A$ onto $K$, a field $F'$ with an $L$-algebra structure, and an algebra structure of the residue field of $A$ on $F$, such that: the structure map from the residue field of $A$ to $F$ is $e$ followed by the structure map $K \to F$; some $x \in F'$ is transcendental over $L$ with $F'$ finite-dimensional over $L(x)$; and there is a term $R$ of the structure `ConstantReduction A F' F` with `R.IsGood`. Such a term consists of a valuation subring $\mathcal{O}$ of $F'$, a ring homomorphism $\mathrm{res} : \mathcal{O} \to F$ and a map from places of $F'/L$ to places of $F/\mathrm{ResidueField}(A)$, subject to: for $x \in L$, the image of $x$ in $F'$ lies in $\mathcal{O}$ if and only if $x \in A$; $\mathrm{res}$ is surjective with kernel the maximal ideal of $\mathcal{O}$; $\mathrm{res}$ is compatible with reduction of $A$ along $\mathrm{ResidueField}(A) \to F$; every nonzero $f \in F'$ can be scaled by some $c \in L$ into $\mathcal{O}$ with nonzero residue; the map on places preserves degrees; and for $f \in \mathcal{O}$ with $\mathrm{res}\,f \neq 0$ the pushforward of the divisor of $f$ is the divisor of $\mathrm{res}\,f$. `R.IsGood` says that the genus $\dim_{\mathrm{ResidueField}(A)} H^1(0)$ of $F/\mathrm{ResidueField}(A)$ equals the genus of $F'/L$.
--
--   This is Deuring's existence of a good constant reduction realising a given one-variable function field over an algebraically closed field as the reduction of one in characteristic zero, the function-field form of the liftability of smooth curves to the Witt vectors. It is used to transport results from characteristic zero, and is cited in the proof of the bound $p^{2g} \le \#\mathrm{Pic}^0[p]$-type torsion estimate [`AlgebraicCurve.Pic0.pow_two_mul_genusFF_le_natCard_torsion_prime_of_natCast_ne_zero`](thm.html#AlgebraicCurve.Pic0.pow_two_mul_genusFF_le_natCard_torsion_prime_of_natCast_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_charZero_constantReduction_isGood.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

universe u v

theorem AlgebraicCurve.exists_charZero_constantReduction_isGood
    (K : Type u) (F : Type v) [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (hF : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L) (_ : CharZero L) (A : ValuationSubring L)
      (e : IsLocalRing.ResidueField A ≃+* K)
      (F' : Type u) (_ : Field F') (_ : Algebra L F') (_ : Algebra (IsLocalRing.ResidueField A) F),
      algebraMap (IsLocalRing.ResidueField A) F = (algebraMap K F).comp e.toRingHom ∧
        (∃ x : F', Transcendental L x ∧
          FiniteDimensional (IntermediateField.adjoin L ({x} : Set F')) F') ∧
        ∃ R : ConstantReduction A F' F, R.IsGood := by sorry
