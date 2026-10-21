-- Prove2me | Theorems.Thm_FiniteFields_Dwork_coefficientFieldFrobenius_coefficientRing
-- name    : FiniteFields.Dwork.coefficientFieldFrobenius_coefficientRing
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T01:41:29.83741+00:00
-- url     : https://prove2.me/theorems/2bee97ac-700a-49f4-8736-e9c01a01928c
-- title:
--   The Frobenius of the coefficient field $K$ restricts to the Witt vector Frobenius on $W(k)$
-- statement:
--   Let $k$ be a finite field of characteristic $p$, let $W(k)$ be its ring of $p$-typical Witt vectors and $F\colon W(k)\to W(k)$ the Witt vector Frobenius (a ring automorphism, since $k$ is perfect). Let $K$ be the completion of the fraction field of $W(k)$ for the discrete valuation attached to its maximal ideal $pW(k)$, and let $\iota\colon W(k)\to K$ be the canonical embedding. The Frobenius of the fraction field preserves this valuation, hence extends to a continuous ring automorphism $\sigma\colon K\to K$. Then for every $x\in W(k)$,
--   $$\sigma\big(\iota(x)\big)=\iota\big(F(x)\big).$$
--
--   So $\sigma$ is the Frobenius automorphism of Dwork's unramified coefficient field, and it is compatible with the Witt vector Frobenius on the ring of integers. This compatibility is what allows computations of $\sigma$ on Teichmüller representatives and on Witt vector expressions to be transported into the complete field.
--
--   **Formalization Note** Since $W(k)$ is already complete, $K$ is isomorphic to $W(k)[1/p]$, the unramified extension of $\mathbb Q_p$ of degree $[k:\mathbb F_p]$; the formalization nevertheless builds $K$ as the uniform-space completion of `FractionRing (WittVector p k)` for the valuation normalized by $v(p)=e^{-1}$, and defines $\sigma$ as the completion of the fraction-field Frobenius.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, §1 (the Frobenius automorphism $\sigma$ of the unramified coefficient field); auxiliary lemma in the formalization of §1, with no separately numbered counterpart in the paper. Lean: ported from the `finite_fields` project (commit e8b5bf14), file `WeilConjectures/Dwork/CoefficientField.lean`, declaration `WeilConjectures.Dwork.coefficientFieldFrobenius_coefficientRing`

import Mathlib
import Definitions.Def_FiniteFields_Dwork_Foundations

open scoped WithZero
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]

theorem FiniteFields.Dwork.coefficientFieldFrobenius_coefficientRing (x : CoefficientRing k p) :
    coefficientFieldFrobenius k p (coefficientRingAlgebraMap k p x) =
      coefficientRingAlgebraMap k p (frobeniusLiftEquiv k p x) := by sorry
