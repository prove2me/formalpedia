-- Prove2me | Theorems.Thm_AlgebraicCurve_isUnit_det_jetMatrix_iff_span_inf_riemannRochSpace_eq_bot
-- name    : AlgebraicCurve.isUnit_det_jetMatrix_iff_span_inf_riemannRochSpace_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/962dec56-c60a-5ed8-8044-0d6c5d8d4382
-- title:
--   Jet matrix invertible iff span meets L(A-sum Pᵢ) trivially
-- statement:
--   Let $K \subseteq F$ be fields, where a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself and a principal ideal ring, and a divisor is a finitely supported $\mathbb{Z}$-valued function on places; $\mathrm{riemannRochSpace}\,D$ is the $K$-subspace of $f \in F$ with $v(f) \le \exp(D\,v)$ for every place $v$. Fix a divisor $A$, a natural number $M$, a family $f : \mathrm{Fin}\,M \to F$ that is linearly independent over $K$ with every $f_j \in L(A)$, places $P_i$, elements $t_i \in F$ and orders $e_i \in \mathbb{N}$ for $i \in \mathrm{Fin}\,M$. Assume the confluent pattern condition: $P_i = P_{i'}$ implies $t_i = t_{i'}$; $P_i = P_{i'}$ together with $e_i = e_{i'}$ implies $i = i'$; and each $e_i$ is smaller than the number of indices $i'$ with $P_{i'} = P_i$. Assume further that each $P_i$ is rational (the map from $K$ to its residue field is surjective), that $\mathrm{ord}_{P_i}(t_i) = 1$, and that $A(P_i) = 0$. Then the determinant of the $M \times M$ matrix over $K$ with $(i,j)$ entry the $e_i$-th Taylor coefficient of $f_j$ at $P_i$ with respect to $t_i$ is a unit if and only if the intersection of the $K$-span of the $f_j$ with $L(A - \sum_i P_i)$ is zero, the places being counted with multiplicity as rows.
--
--   This is the Hermite-interpolation, or generalised Wronskian, rank criterion for a linearly independent sub-system of a Riemann–Roch space: the rows of the jet matrix evaluate the functionals reading all Taylor coefficients of order below the row multiplicity at each place, whose joint kernel inside $L(A)$ is $L(A - \sum_i P_i)$. Note that the criterion is stated for the span of the given family rather than for the vanishing of $L(A - \sum_i P_i)$ itself, the two agreeing when the $f_j$ span $L(A)$. It is used in the height and mass estimates on the modular curve side, via [`ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le`](thm.html#ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_isUnit_det_jetMatrix_iff_span_inf_riemannRochSpace_eq_bot.lean

import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.isUnit_det_jetMatrix_iff_span_inf_riemannRochSpace_eq_bot
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (A : Divisor K F) {M : ℕ} (f : Fin M → F) (hf : LinearIndependent K f)
    (hfA : ∀ j, f j ∈ riemannRochSpace A)
    (P : Fin M → Place K F) (t : Fin M → F) (e : Fin M → ℕ)
    (hP : IsConfluentPattern P t e) (hrat : ∀ i, (P i).IsRational)
    (ht : ∀ i, (P i).ord (t i) = 1) (hA : ∀ i, A (P i) = 0) :
    IsUnit (jetMatrix P t e f).det ↔
      Submodule.span K (Set.range f) ⊓ riemannRochSpace (A - jetDivisor P) = ⊥ := by sorry
