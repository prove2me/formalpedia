-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_isAlgClosed
-- name    : AlgebraicCurve.RegularProlongation.exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/aa3fcb89-58a4-5f1a-b169-8caaf19fec4d
-- title:
--   Rigidity of q-th roots under good regular prolongations
-- statement:
--   Let $L$ be an algebraically closed field, $A\subseteq L$ a valuation subring with residue field $k=\mathrm{ResidueField}\,A$, and $F$ a field extension of $L$ which is a function field of one variable in the sense that some $x\in F$ is transcendental over $L$ with $F$ finite-dimensional over $L(x)$. Let $\bar F$ be a field extension of $k$ and let $R$ be a regular prolongation of $A$ to $F$ with residue field $\bar F$: that is, a valuation subring $\mathcal O=R.\mathrm{integers}$ of $F$ together with a ring homomorphism $\rho=R.\mathrm{residue}\colon\mathcal O\to\bar F$ such that for $c\in L$ one has $c\in A$ iff its image lies in $\mathcal O$, $\rho$ is surjective with kernel the maximal ideal of $\mathcal O$, $\rho$ restricted to $A$ is the composite of $A\to k$ with $k\to\bar F$, and every nonzero $f\in F$ admits $c\in L$ with $c\cdot f\in\mathcal O$ and $\rho(c\cdot f)\neq 0$. Assume the prolongation is good, $\mathrm{genusFF}(k,\bar F)=\mathrm{genusFF}(L,F)$, where $\mathrm{genusFF}(K,E)$ is the $K$-dimension of $H^1$ of the zero divisor of $E/K$; and assume it is defectless at some $x\in\mathcal O$: $\rho(x)$ is transcendental over $k$, $0<[\bar F:k(\rho(x))]$, and $[F:L(x)]=[\bar F:k(\rho(x))]$. Let $q$ be prime with $q\neq 0$ in $k$, and let $f\in\mathcal O$ be such that $q$ divides $\mathrm{ord}_P(f)$ for every place $P$ of $F/L$ (a proper valuation subring of $F$ containing $L$ whose ring is a principal ideal ring, $\mathrm{ord}$ being minus the logarithm of its adic valuation), and such that $\rho(f)=w^q$ for some $w\in\bar F$, $w\neq 0$. Then $f=h^q$ for some $h\in F$.
--
--   This is the rigidity lemma of Deuring's theory of reduction of algebraic function fields: for a good, defectless regular prolongation, a function whose divisor is divisible by $q$ and whose reduction is a nonzero $q$-th power is itself a $q$-th power. No characteristic hypothesis on $L$ is imposed, only $q\neq 0$ in the residue field $k$. It is used in the analysis of constant reduction, where it feeds the injectivity on $q$-torsion of the reduction map on degree-zero divisor classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_isAlgClosed
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
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
