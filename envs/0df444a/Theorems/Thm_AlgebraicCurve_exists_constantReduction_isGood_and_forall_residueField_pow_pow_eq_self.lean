-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_constantReduction_isGood_and_forall_residueField_pow_pow_eq_self
-- name    : AlgebraicCurve.exists_constantReduction_isGood_and_forall_residueField_pow_pow_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/bec4b75f-6193-5472-b1f0-2ed5c937a38e
-- title:
--   Existence of a good constant reduction, after Deuring
-- statement:
--   Let $K$ be an algebraically closed field with exponential characteristic $p$, and let $F$ be a field extension of $K$ which is a one-variable function field in the sense that some $x \in F$ is transcendental over $K$ with $F$ finite-dimensional over $K(x)$, and which satisfies `IsCurveOver K F`: every nonzero $f \in F$ has a divisor of degree $0$ recording its orders at all places, each place of $F/K$ has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank $1$ over $F$. Then there are a valuation subring $A \subseteq K$, a field $\bar F$ (in the universe of $F$) over the residue field $k = A/\mathfrak m_A$, together with proofs that $k$ is algebraically closed and that `IsCurveOver k \bar F` holds, and a constant reduction $R \in$ `ConstantReduction A F \bar F` — that is, a valuation subring $\mathcal{O}$ of $F$ with $\operatorname{algebraMap} x \in \mathcal{O} \iff x \in A$ for $x \in K$, a surjective ring homomorphism $\mathcal{O} \to \bar F$ with kernel the maximal ideal of $\mathcal{O}$ and compatible with $A \to k \to \bar F$, such that every nonzero $f \in F$ admits $c \in K$ with $cf \in \mathcal{O}$ of nonzero residue, plus a degree-preserving map on places carrying the divisor of any $f \in \mathcal{O}$ with nonzero residue to the divisor of its residue — such that: $R$ is good, i.e. $\operatorname{genusFF} k\,\bar F = \operatorname{genusFF} K\,F$ (equality of the $K$-dimensions of $H^1(0)$); every $a \in k$ satisfies $a^{p^n} = a$ for some $n > 0$; and $\bar F$ is again a one-variable function field over $k$, some $y \in \bar F$ being transcendental over $k$ with $\bar F$ finite-dimensional over $k(y)$.
--
--   This is Deuring's theorem on constant reduction of function fields, specialised to a place of the algebraically closed constant field $K$ whose residue field is algebraic over the prime field (in characteristic zero the trivial valuation and the identity reduction suffice). It is used to transfer questions about the degree-zero divisor class group of $F/K$ to a curve over a residue field all of whose elements are roots of unity or zero, and is cited in the proofs that the torsion of $\mathrm{Pic}^0$ is finite and that its $\ell$-primary part has order $\ell^{2g}$ when $\ell$ is invertible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_constantReduction_isGood_and_forall_residueField_pow_pow_eq_self.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

universe u v

theorem AlgebraicCurve.exists_constantReduction_isGood_and_forall_residueField_pow_pow_eq_self
    (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    (p : ℕ) [ExpChar K p]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F] :
    ∃ (A : ValuationSubring K) (Fbar : Type v) (_ : Field Fbar)
      (_ : Algebra (IsLocalRing.ResidueField A) Fbar)
      (_ : IsAlgClosed (IsLocalRing.ResidueField A))
      (_ : IsCurveOver (IsLocalRing.ResidueField A) Fbar)
      (R : ConstantReduction A F Fbar),
      R.IsGood ∧
        (∀ a : IsLocalRing.ResidueField A, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a) ∧
          ∃ y : Fbar, Transcendental (IsLocalRing.ResidueField A) y ∧
            FiniteDimensional
              (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({y} : Set Fbar)) Fbar := by sorry
