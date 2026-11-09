-- Prove2me | Theorems.Thm_CommutativeRankNC_Approximation_lemma_2_1
-- name    : CommutativeRankNC.Approximation.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:09.417201+00:00
-- url     : https://prove2.me/theorems/37a70eae-d366-48e4-a90c-26d1e7fd2d2e
-- title:
--   Lemma 2.1 — Irreducible polynomial and field arithmetic
-- statement:
--   For $m\ge2$, let $r_f=\lceil\log_2m\rceil$ and $q=2^{r_f}$. The first monic polynomial $f$ passing the finite trial-division search is irreducible and has degree $r_f$. One deterministic logspace-uniform Boolean NC² family computes its coefficient code and addition, multiplication and inversion in $\mathbb F_2[z]/(f)$ for every pair of $r_f$-bit operands:
--
--   $$f\text{ monic and irreducible},\quad\deg f=r_f,\quad a\ne0\Longrightarrow aa^{-1}=1.$$
--
--   Complexity is measured in $m$. Inversion at zero is totalized to zero; the inverse identity is required only on nonzero elements. This supplies the field arithmetic for the sign construction.
--
--   Differences from the source:
--   - encoding: elements of the quotient field F₂[z]/(f) → binary coefficient representatives, finite trial division, and reduction modulo the first irreducible polynomial; reason: these are the explicit field representation and deterministic search in the proof of Lemma 2.1; no arithmetic oracle is used
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), Lemma 2.1, PDF/printed p.9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_ConstructionCodes

namespace CommutativeRankNC.Approximation

/-- Lemma 2.1, PDF/printed p.9: the first trial-division candidate is an
irreducible monic degree-r polynomial, and its bit-represented field arithmetic
is performed by one uniform Boolean NC² family on all operands and sizes. -/
theorem lemma_2_1 :
    ∃ F : (N : ℕ) → BooleanCircuit N, BooleanNC 2 F ∧
      ∀ m : ℕ, 2 ≤ m →
        (fieldPolynomial m).Monic ∧
        (fieldPolynomial m).natDegree = fieldDegree m ∧
        Irreducible (fieldPolynomial m) ∧
        (∀ a < fieldCard m, a ≠ 0 → fieldMul m a (fieldInv m a) = 1) ∧
        ∀ a < fieldCard m, ∀ b < fieldCard m,
          booleanEval (F (fieldInputCode m a b).length) (fieldInputCode m a b) =
            fieldOutputCode m a b := by sorry

end CommutativeRankNC.Approximation
