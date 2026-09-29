-- Prove2me | Theorems.Thm_AlgebraicCurve_RROpens_exists_forall_hasValue_forall_ord_nonneg
-- name    : AlgebraicCurve.RROpens.exists_forall_hasValue_forall_ord_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/aac2fe64-a8fb-5307-944b-58e01f0e4b04
-- title:
--   Interpolation with prescribed non-zero values and one pole
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field that is a $K$-algebra, satisfying `IsCurveOver K F`: principal divisors exist (every $f \in F$ with $f \neq 0$ admits a finitely supported divisor $D$ with $D(v) = \operatorname{ord}_v f$ at every place $v$ and $\deg D = 0$), every place has residue field finite over $K$, and $\Omega[F/K]$ is free of rank one over $F$; here a place is a valuation subring of $F$ containing the image of $K$, proper in $F$ and a principal ideal ring, and $\operatorname{ord}_v f$ is minus the logarithm of its adic valuation. Fix a divisor $Kc$ (a finitely supported $\mathbb{Z}$-valued function on places) and $g \in \mathbb{N}$ such that the Riemann–Roch equality $\ell(D) - \ell(Kc - D) = \deg D + 1 - g$ holds for every divisor $D$, where $\ell(D)$ is the $K$-dimension of the Riemann–Roch space of $D$ and $\deg$ is the degree homomorphism weighting $D(v)$ by the residue degree of $v$. Let $E$ be a finite set of places, $c$ a $K$-valued function on places with $c(e) \neq 0$ for all $e \in E$, and $P_0$ a place not in $E$. Then there is $h \in F$, $h \neq 0$, such that for each $e \in E$ the element $h$ lies in the valuation subring of $e$ and its residue there is the image of $c(e)$, and such that $\operatorname{ord}_v h \geq 0$ for every place $v \neq P_0$.
--
--   This is the interpolation (weak strong-approximation) statement for a curve: a function regular away from a single prescribed place $P_0$ and taking prescribed non-zero values at finitely many other places, so that it is a unit at each of those places. It is used to produce functions realising prescribed gluing data, for instance in [`AlgebraicCurve.GluedPic0.mem_closure_mk_pair_of_riemannRoch`](thm.html#AlgebraicCurve.GluedPic0.mem_closure_mk_pair_of_riemannRoch) and in the construction of good classes and fixed glue data for place specialisations on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RROpens_exists_forall_hasValue_forall_ord_nonneg.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.RROpens.exists_forall_hasValue_forall_ord_nonneg
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F] (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (E : Finset (Place K F)) (c : Place K F → K) (hc : ∀ e ∈ E, c e ≠ 0)
    (P₀ : Place K F) (hP₀ : P₀ ∉ E) :
    ∃ h : F, h ≠ 0 ∧ (∀ e ∈ E, e.HasValue h (c e)) ∧
      ∀ v : Place K F, v ≠ P₀ → 0 ≤ v.ord h := by sorry
