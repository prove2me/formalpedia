-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_monic_coeff_natDegree_le_of_forall_valuationSubring
-- name    : AlgebraicCurve.RegularProlongation.exists_monic_coeff_natDegree_le_of_forall_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/75ecaa4e-26f0-5e53-ba25-890b68c2fb63
-- title:
--   Monic equation with Gauss degree bounds over a regular prolongation
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, $F$ a field extension of $L$, and $Fbar$ a field extension of the residue field of $A$. Let $R$ be a regular prolongation of $A$ to $F$ with residue field $Fbar$: that is, a valuation subring $R.integers$ of $F$ together with a ring homomorphism $R.residue : R.integers \to Fbar$ such that an element of $L$ lies in $A$ exactly when its image in $F$ lies in $R.integers$, $R.residue$ is surjective with kernel the maximal ideal of $R.integers$, $R.residue$ agrees on elements coming from $A$ with the map induced by the residue map of $A$ and the algebra structure of $Fbar$, and every nonzero $f \in F$ can be scaled by some $c \in L$ so that $c \cdot f$ lies in $R.integers$ with nonzero residue. Let $x \in R.integers$ have residue transcendental over the residue field of $A$, let $f \in F$ and $m \in \mathbb{N}$, and assume: (h₁) $f$ lies in every valuation subring $V$ of $F$ that contains the image of $L$ and contains $x$; (h₂) $f \cdot (x^m)^{-1}$ lies in every valuation subring $V$ of $F$ containing the image of $L$ but not $x$; (h₃) $f$ lies in every valuation subring $V$ of $F$ whose intersection with $L(x)$, the intermediate field $\mathrm{IntermediateField.adjoin}\ L\ \{x\}$, agrees with that of $R.integers$. Then there is a polynomial $p \in A[X][T]$ which is monic in $T$, whose $j$-th coefficient $p_j \in A[X]$ satisfies $\deg p_j \le (\deg_T p - j) \cdot m$ for every $j$ (truncated subtraction in $\mathbb{N}$), and which vanishes when $X$ is evaluated at $x$ (via $A \hookrightarrow L \to F$) and $T$ at $f$.
--
--   This is the Gauss-norm integrality equation of Deuring's theory of reduction of function fields: the three hypotheses express that $f$ lies in the Riemann–Roch space attached to $m$ times the pole divisor of $x$ and in the prolonged valuation ring, and the conclusion produces an integral equation for $f$ over $A[x]$ with the expected bounds on the $x$-degrees of the coefficients. It is the basic tool in the subsequent construction of finite sets of places over which a prescribed $L$-space reduces well, and is invoked by the results on bases and spans of such spaces modulo the maximal ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_monic_coeff_natDegree_le_of_forall_valuationSubring.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_monic_coeff_natDegree_le_of_forall_valuationSubring
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (f : F) (m : ℕ)
    (h₁ : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → (x : F) ∈ V → f ∈ V)
    (h₂ : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → (x : F) ∉ V →
      f * ((x : F) ^ m)⁻¹ ∈ V)
    (h₃ : ∀ V : ValuationSubring F,
      (∀ e : F, e ∈ IntermediateField.adjoin L {(x : F)} → (e ∈ V ↔ e ∈ R.integers)) → f ∈ V) :
    ∃ p : Polynomial (Polynomial A), p.Monic ∧
      (∀ j, (p.coeff j).natDegree ≤ (p.natDegree - j) * m) ∧
      p.eval₂ (Polynomial.eval₂RingHom ((algebraMap L F).comp A.subtype) (x : F)) f = 0 := by sorry
