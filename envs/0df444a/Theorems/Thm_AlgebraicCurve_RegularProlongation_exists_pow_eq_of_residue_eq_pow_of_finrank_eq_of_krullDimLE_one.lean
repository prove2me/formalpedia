-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one
-- name    : AlgebraicCurve.RegularProlongation.exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/10fd2e65-5db0-53ba-82b5-cc985b588c6d
-- title:
--   Rigidity of q-th roots under good regular reduction (rank one)
-- statement:
--   Let $L$ be an algebraically closed field of characteristic $0$ and $A \subseteq L$ a valuation subring whose Krull dimension is at most $1$, with residue field $k = \mathrm{ResidueField}\,A$. Let $F$ be a field extension of $L$ admitting some $x$ transcendental over $L$ with $F$ finite-dimensional over $L(x)$, and let $\bar F$ be a field extension of $k$. Let $R$ be a regular prolongation of $A$ to $F$ with residue field $\bar F$: a valuation subring $\mathcal O = R.\mathrm{integers}$ of $F$ together with a ring homomorphism $\rho = R.\mathrm{residue} : \mathcal O \to \bar F$ such that for $c \in L$ one has $c \in \mathcal O$ exactly when $c \in A$, $\rho$ is surjective with kernel the maximal ideal of $\mathcal O$, $\rho$ agrees on $A$ with $A \to k \to \bar F$, and every nonzero $f \in F$ has a constant multiple $c f \in \mathcal O$ with $\rho(cf) \neq 0$. Assume the prolongation is good, $\mathrm{genusFF}(k,\bar F) = \mathrm{genusFF}(L,F)$ (the genus being the dimension over the constant field of $H^1$ of the zero divisor), and regular at some element: there is $x \in \mathcal O$ with $\rho(x)$ transcendental over $k$, $0 < [\bar F : k(\rho(x))]$ and $[F : L(x)] = [\bar F : k(\rho(x))]$. Let $q$ be a prime that is nonzero in $k$. Then for every $f \in \mathcal O$ such that $q \mid P.\mathrm{ord}(f)$ for every place $P$ of $F/L$ (a valuation subring of $F$ containing $L$, not all of $F$, whose valuation ring is a principal ideal ring, the order being taken with respect to its adic valuation), and such that $\rho(f) = w^q$ for some $w \neq 0$ in $\bar F$, there exists $h \in F$ with $h^q = f$.
--
--   This is the rank-one form of Deuring's rigidity statement for $q$-th roots in a function field with good reduction: divisibility of all local orders by $q$ together with the existence of a $q$-th root of the residue forces a $q$-th root in $F$ itself. It is used in the study of reductions of modular curves, where it supports the statements [`ModularCurve.eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero`](thm.html#ModularCurve.eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero) and [`ModularCurve.eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero`](thm.html#ModularCurve.eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero); the proof cites the Kummer degree computation [`AlgebraicCurve.KummerCover.finrank_eq`](thm.html#AlgebraicCurve.KummerCover.finrank_eq), the genus formula for Kummer covers [`AlgebraicCurve.genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord`](thm.html#AlgebraicCurve.genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord), the construction of prolongations [`AlgebraicCurve.RegularProlongation.exists_prolongation_of_card_roots_eq`](thm.html#AlgebraicCurve.RegularProlongation.exists_prolongation_of_card_roots_eq), and the rank-one genus inequality [`AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one`](thm.html#AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    [Ring.KrullDimLE 1 A]
    {F : Type*} [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (hgood : genusFF (IsLocalRing.ResidueField A) Fbar = genusFF L F)
    (hreg : ∃ x : R.integers, Transcendental (IsLocalRing.ResidueField A) (R.residue x) ∧
      0 < Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar ∧
      Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
        Module.finrank
          (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    {q : ℕ} [Fact q.Prime] (hq : (q : IsLocalRing.ResidueField A) ≠ 0)
    (f : R.integers) (hdvd : ∀ P : Place L F, (q : ℤ) ∣ P.ord (f : F))
    (w : Fbar) (hw0 : w ≠ 0) (hw : w ^ q = R.residue f) :
    ∃ h : F, h ^ q = (f : F) := by sorry
