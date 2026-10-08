-- Prove2me | Theorems.Thm_AdaGrad_Full_lemma_13
-- name    : AdaGrad.Full.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:44:34.754195+00:00
-- url     : https://prove2.me/theorems/56503d03-75f2-416e-a035-e3f42c0a8cc5
-- title:
--   Lemma 13 — the matrix square root is operator monotone
-- statement:
--   Let $A$ and $B$ be real symmetric $d\times d$ matrices with $A\succeq B\succeq0$ (Loewner order: $A-B$ and $B$ positive semidefinite). Then their positive semidefinite square roots satisfy
--   $$A^{1/2}\succeq B^{1/2}.$$
--
--   The paper uses it to see that $G_t^{1/2}$ is non-decreasing in $t$ (so the proximal functions of Figure 2 grow) and inside the proofs of Lemmas 8 and 9.
--
--   **Formalization Note** $A^{1/2}$ is Mathlib's `CFC.sqrt`. Mathlib proves this monotonicity (`CFC.sqrt_le_sqrt`) only in C*-algebras, which covers complex matrices but not real ones, so the real case is posed here.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), p. 2148, Lemma 13

import Mathlib
import Definitions.Def_AdaGrad_Full_Algorithm2
open scoped MatrixOrder InnerProductSpace

namespace AdaGrad.Full

/-- Lemma 13 (p. 2148): the matrix square root is monotone for the Loewner order on real symmetric
positive semidefinite matrices: `A ⪰ B ⪰ 0` implies `A^{1/2} ⪰ B^{1/2}`. -/
theorem lemma_13 {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) (hB : B.PosSemidef)
    (hAB : (A - B).PosSemidef) : (CFC.sqrt A - CFC.sqrt B).PosSemidef := by sorry

end AdaGrad.Full
