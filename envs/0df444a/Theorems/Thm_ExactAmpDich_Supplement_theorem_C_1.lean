-- Prove2me | Theorems.Thm_ExactAmpDich_Supplement_theorem_C_1
-- name    : ExactAmpDich.Supplement.theorem_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:24:46.304743+00:00
-- url     : https://prove2.me/theorems/f25bbc4c-d064-4cf5-9373-0fbb43950474
-- title:
--   Theorem C.1 — finite resource alternative: a computable gadget over $\{U,U^\dagger\}$ with at most 24 occurrences and $O(k)$ wires
-- statement:
--   There are an absolute constant $C$ and an algorithm, given by a computable map on exact codes, with the following property. Let $k\ge1$ and let $U$ be a nonmonomial unitary on $k$ qubits with algebraic entries. On any exact code of $U$ the algorithm returns (the code of) a basis-postselected state gadget over the two-gate library $\{U,U^\dagger\}$ that
--
--   1. uses at most $24$ occurrences of $U$ or $U^\dagger$,
--   2. uses at most $C\cdot k$ wires, and
--   3. produces at least one of: (i) a coherent one-qubit state $s_0|0\rangle+s_1|1\rangle$ with $s_0s_1\ne0$; (ii) a two-qubit state with an invertible symmetric coefficient matrix; (iii) an entangled two-qubit state with unequal Schmidt coefficients.
--
--   This is the starting point of the resource construction: (ii) and (iii) lead to a symmetric unitary pair, and (i) is the input of Theorem D.1.
--
--   Differences from the source:
--   - encoding: a finite algorithm whose every choice is determined by an exact algebraic test → a computable map from exact codes of U to gadget codes, correct on every valid code; reason: exact tests on algebraic numbers are exactly what a computable map on exact codes performs
--   - encoding: O(k) wires → at most C·k wires for one constant C fixed before k and U; reason: the meaning of the O
--   - encoding: unequal Schmidt coefficients → the coefficient matrix A is invertible and AA† is not a scalar multiple of the identity; reason: the Schmidt coefficients are the singular values of A, equal exactly when AA† is scalar
-- source:
--   Liu–Meng, A Dichotomy for Exact Quantum Circuit Amplitudes, STOC 2027 submission (held manuscript, sha256 40ad9c68…), Theorem C.1, p.27 (PDF p.28)

import Mathlib
import Definitions.Def_ExactAmpDich_QTract
import Definitions.Def_ExactAmpDich_Supplement_Codes
import Definitions.Def_ExactAmpDich_Supplement_Gadget

set_option autoImplicit false

namespace ExactAmpDich.Supplement

open QAlgorithms

/-- **Theorem C.1 (Finite resource alternative).** Liu–Meng, *A Dichotomy for Exact Quantum
Circuit Amplitudes*, STOC 2027 submission (held manuscript, sha256 40ad9c68…), Theorem C.1, p.27
(PDF p.28): "Given a nonmonomial algebraic k-qubit unitary U, a finite algorithm constructs a
gadget over {U, U†} producing at least one of the following: (i) a coherent one-qubit state
s0|0⟩ + s1|1⟩ with s0s1 ≠ 0; (ii) a two-qubit state with an invertible symmetric coefficient
matrix; (iii) an entangled two-qubit state with unequal Schmidt coefficients. The gadget uses at
most 24 occurrences of U or U† and O(k) wires. Every choice is determined by an exact algebraic
test."

There are an absolute constant `C` and a computable map from exact codes of matrices to gadget
codes such that, for every `k ≥ 1`, every nonmonomial unitary `U` on `k` qubits and every exact
code of `U`, the output is the code of a basis-postselected state gadget over `{U, U†}` with at
most `24` gate occurrences and at most `C·k` wires whose state satisfies (i), (ii) or (iii).

**Formalization Note.** "O(k) wires" is one constant `C` chosen before `k` and `U`; "a finite
algorithm" whose choices are exact algebraic tests is a computable map on exact codes (every valid
code of `U`). The three outcomes are invariant under nonzero scalars, so the paper's convention of
known nonzero scalar factors changes nothing. -/
theorem theorem_C_1 :
    ∃ (C : ℕ) (alg : MatCode → GadgetCode), Computable alg ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (U : Matrix (Qubits k) (Qubits k) ℂ),
        U ∈ Matrix.unitaryGroup (Qubits k) ℂ → ¬ IsMonomial U →
        ∀ cd : MatCode, MatCode.Denotes k cd U →
          ∃ G : Gadget (twoGate k hk U), alg cd = G.code ∧ G.c.length ≤ 24 ∧ G.n ≤ C * k ∧
            (G.IsCoherentState ∨ G.IsSymmetricEntangledState ∨ G.IsUnequalSchmidtState) := by sorry

end ExactAmpDich.Supplement
