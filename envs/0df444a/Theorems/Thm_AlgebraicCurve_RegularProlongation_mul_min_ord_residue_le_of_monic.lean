-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic
-- name    : AlgebraicCurve.RegularProlongation.mul_min_ord_residue_le_of_monic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/21e1d4e9-e2f7-52c5-9e7c-91be1c569749
-- title:
--   Pole bound for residues under a regular prolongation
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, $F$ a field extension of $L$, and $\bar F$ a field equipped with an algebra structure over the residue field of $A$. Let $R$ be a regular prolongation of $A$ to $F$ with residue field $\bar F$: a valuation subring $\mathcal{O} = R.\mathrm{integers}$ of $F$ together with a surjective ring homomorphism $R.\mathrm{residue} : \mathcal{O} \to \bar F$ whose kernel is the maximal ideal of $\mathcal{O}$, such that an element of $L$ lands in $\mathcal{O}$ exactly when it lies in $A$, the residue map is compatible with $A \to \mathrm{ResidueField}\,A \to \bar F$, and every nonzero $f \in F$ has an $L$-multiple lying in $\mathcal{O}$ with nonzero residue. Let $f, h \in \mathcal{O}$, let $m \in \mathbb{N}$, and let $p \in A[X][T]$ be monic, with $\deg_X p_j \le (\deg_T p - j)\,m$ for every $j$ (truncated subtraction). Assume $p$ vanishes when its coefficients $p_j \in A[X]$ are evaluated at $f$ via $A \hookrightarrow L \to F$ and the outer variable at $h$. Then for every place $w$ of $\bar F$ over the residue field of $A$ — a proper valuation subring of $\bar F$ containing the image of that residue field and a principal ideal ring, with $w.\mathrm{ord}$ minus the logarithm of its associated adic valuation — one has $m \cdot \min(0, w.\mathrm{ord}(\bar f)) \le w.\mathrm{ord}(\bar h)$, where $\bar f, \bar h$ are the residues of $f, h$.
--
--   This is the divisor-reduction step in Deuring's theory of reduction of algebraic function fields at a regular prolongation: an integral equation for $h$ over $A[f]$ with degrees bounded by $m$ forces the residue $\bar h$ to have poles only at poles of $\bar f$, of order at most $m$ times the pole order, i.e. $\bar h$ lies in the Riemann–Roch space of $m\,(\bar f)_\infty$. It is used in the constructions of finite sets of places and of families whose residues are linearly independent, such as [`AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_forall_lSpace_le_span_and_linearIndependent_residue`](thm.html#AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_forall_lSpace_le_span_and_linearIndependent_residue), and in [`AlgebraicCurve.RegularProlongation.mul_min_ord_residue_le_of_forall_valuationSubring_mem`](thm.html#AlgebraicCurve.RegularProlongation.mul_min_ord_residue_le_of_forall_valuationSubring_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.mul_min_ord_residue_le_of_monic
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (f h : R.integers) (m : ℕ)
    (p : Polynomial (Polynomial A)) (hp : p.Monic)
    (hdeg : ∀ j, (p.coeff j).natDegree ≤ (p.natDegree - j) * m)
    (hroot : p.eval₂ (Polynomial.eval₂RingHom ((algebraMap L F).comp A.subtype) (f : F))
      (h : F) = 0)
    (w : Place (IsLocalRing.ResidueField A) Fbar) :
    (m : ℤ) * min 0 (w.ord (R.residue f)) ≤ w.ord (R.residue h) := by sorry
