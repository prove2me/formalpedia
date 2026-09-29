-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_ordDifferential_eq_neg_one_of_ne
-- name    : AlgebraicCurve.exists_ordDifferential_eq_neg_one_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/1107c4b0-08f6-5224-a188-31b3670060cc
-- title:
--   Existence of a differential of the third kind
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, $K$ algebraically closed, and assume: the project's curve package `IsCurveOver K F`, i.e. every nonzero $f \in F$ has a divisor $\sum_v \operatorname{ord}_v(f)\,v$ of degree $0$, each residue field of a place is finite over $K$, and $\Omega_{F/K}$ is free of rank one over $F$; `HasCanonicalDivisor`, i.e. for every nonzero $\omega \in \Omega_{F/K}$ the function $v \mapsto \operatorname{ord}_v(\omega)$ has finite support, so defines a divisor $\operatorname{canonicalDivisorOf}$; at every place $v$ the differential $d\pi_v$ of a uniformiser spans $\Omega_{F/K}$ over $F$ (`DCoordGenerates`); and $\Omega_{F/K}$ is nontrivial. Here places are valuation subrings of $F$, proper, containing $K$ and with principal-ideal valuation ring, and $\operatorname{ord}_v(\omega)$ (`Place.ordDifferential`) means the valuation at $v$ of the coefficient $f$ in $\omega = f \cdot d\pi_v$. Assume further the hypothesis `hRR` that Riemann–Roch holds in the form $\ell(D) - \ell((\omega_0) - D) = \deg D + 1 - g$ for every nonzero $\omega_0$ and every divisor $D$, with $g$ the project's genus read off from the degree of a canonical divisor. Then for any two distinct places $P \neq Q$ there is a nonzero $\omega \in \Omega_{F/K}$ with $\operatorname{ord}_P(\omega) = \operatorname{ord}_Q(\omega) = -1$ and $\operatorname{ord}_v(\omega) \geq 0$ for every place $v$ other than $P$ and $Q$.
--
--   This is the classical existence statement for a differential of the third kind: on a curve over an algebraically closed field, a nonzero differential with simple poles exactly at two prescribed distinct places and no other poles. It is used in the construction of residue-type pairings on modular curves, being cited in the project's results on divisors of degree zero and on the existence of slash-invariant functions with prescribed nonvanishing residues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_ordDifferential_eq_neg_one_of_ne.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RiemannRochRows

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.exists_ordDifferential_eq_neg_one_of_ne {K F : Type*} [Field K] [Field F]
    [Algebra K F] [IsAlgClosed K] [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : Place K F, w.DCoordGenerates] [Nontrivial (Ω[F⁄K])]
    (hRR : FunctionFieldRiemannRoch K F) {P Q : Place K F} (hPQ : P ≠ Q) :
    ∃ ω : Ω[F⁄K], ω ≠ 0 ∧ P.ordDifferential ω = -1 ∧ Q.ordDifferential ω = -1 ∧
      ∀ v : Place K F, v ≠ P → v ≠ Q → 0 ≤ v.ordDifferential ω := by sorry
