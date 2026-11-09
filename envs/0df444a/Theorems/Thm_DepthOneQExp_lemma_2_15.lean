-- Prove2me | Theorems.Thm_DepthOneQExp_lemma_2_15
-- name    : DepthOneQExp.lemma_2_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:47:56.529857+00:00
-- url     : https://prove2.me/theorems/7b874b4f-fc5a-467e-9873-f35d76465c9d
-- title:
--   Lemma 2.15: the commutant of the CNOT gates is $\mathrm{Span}\{I, |+^n\rangle\langle+^n|, |0^n\rangle\langle0^n|, |0^n\rangle\langle+^n|, |+^n\rangle\langle0^n|\}$
-- statement:
--   A $2^n\times 2^n$ complex matrix $M$ commutes with every CNOT gate $\mathrm{CNOT}_{a,b}$ ($a\ne b$) if and only if
--   $$
--   M \in \mathrm{Span}\{\,I_{2^n},\ |+^n\rangle\langle+^n|,\ |0^n\rangle\langle0^n|,\ |0^n\rangle\langle+^n|,\ |+^n\rangle\langle0^n|\,\}.
--   $$
--
--   Applied to the operator $\mathbb E_{P\sim\mu(G_n)}P\otimes P$ (read as a matrix through vectorization), it identifies the range of the second-moment operator of the CNOT group as the span of $|a_1\rangle,\dots,|a_5\rangle$.
--
--   **Formalization Note** The span is the complex linear span; $|u\rangle\langle v|$ is the outer product $u\,v^\dagger$.
--
--   Differences from the source: none.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Lemma 2.15, Eq. (2.29), p.12

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_permToMatrix
import Definitions.Def_DepthOneQExp_cnotPerm
import Definitions.Def_DepthOneQExp_plusVec
import Definitions.Def_DepthOneQExp_zeroVec

namespace DepthOneQExp

/-- Lemma 2.15 (Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group
and applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, Lemma 2.15, Eq. (2.29),
p.12): a `2ⁿ × 2ⁿ` matrix commutes with every CNOT gate if and only if it lies in
`Span{I, |+ⁿ⟩⟨+ⁿ|, |0ⁿ⟩⟨0ⁿ|, |0ⁿ⟩⟨+ⁿ|, |+ⁿ⟩⟨0ⁿ|}`.

**Formalization Note** "CNOT gate" ranges over `CNOT_{a,b}` for all qubits `a ≠ b`; `|u⟩⟨v|` is
`Matrix.vecMulVec u (star v)`; the span is the complex linear span. -/
theorem lemma_2_15 (n : ℕ) (M : Matrix (MITMSynthesis.Q n) (MITMSynthesis.Q n) ℂ) :
    (∀ a b : Fin n, a ≠ b →
      M * permToMatrix (cnotPerm n a b) = permToMatrix (cnotPerm n a b) * M) ↔
    M ∈ Submodule.span ℂ
      ({1, Matrix.vecMulVec (plusVec n) (star (plusVec n)),
        Matrix.vecMulVec (zeroVec n) (star (zeroVec n)),
        Matrix.vecMulVec (zeroVec n) (star (plusVec n)),
        Matrix.vecMulVec (plusVec n) (star (zeroVec n))} :
        Set (Matrix (MITMSynthesis.Q n) (MITMSynthesis.Q n) ℂ)) := by sorry

end DepthOneQExp
