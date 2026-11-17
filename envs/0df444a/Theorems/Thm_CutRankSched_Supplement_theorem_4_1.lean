-- Prove2me | Theorems.Thm_CutRankSched_Supplement_theorem_4_1
-- name    : CutRankSched.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:50:59.282056+00:00
-- url     : https://prove2.me/theorems/9bdd8bae-2c13-4686-a24a-5c7a76061b91
-- title:
--   Theorem 4.1 — exact signed Clifford-frame extraction
-- statement:
--   Let $U$ be the unitary of a Clifford+$T/T^\dagger$ circuit on $m$ qubits, and let $(\epsilon_1,p_1),\dots,(\epsilon_n,p_n)$ be the signed Pauli labels computed from the circuit by Clifford-tableau updates (the extraction recursion). Then
--
--   1. $n$ is the number of $T/T^\dagger$ gates of the circuit, and every $p_i\neq 0$;
--   2. there are a Clifford operator $F$ and a global phase $u$ with $|u|=1$ such that
--   $$
--   U = u\,F\,R_{\epsilon_n}(P(p_n))\cdots R_{\epsilon_1}(P(p_1)). \tag{4}
--   $$
--
--   This turns any Clifford+$T$ circuit into the fixed trace of signed Pauli rotations that the scheduling model of Problem 3.2 takes as input, without cancelling or merging any non-Clifford occurrence.
--
--   Differences from the source:
--   - reading: a fixed Hermitian representative P(p) of the Pauli operator of p → P(p) = i^{x·z} X^x Z^z, the tensor product of I, X, Y, Z prescribed by p; reason: the source fixes a representative without naming it; this is the standard one
--   - encoding: R_ε(P) = exp(−iεπP/8) → cos(π/8)·1 − iε sin(π/8)·P; reason: equal whenever P² = 1, which holds for every P(p)
--   - encoding: Clifford+T/T† circuit on m qubits → list of gates H_q, S_q, CNOT_{c,t}, T_q, T†_q, first gate acting first; reason: H, S, CNOT generate the Clifford group up to global phase; the source's right-to-left convention
--   - reading: the signs and Pauli labels can be computed exactly by Clifford-tableau updates without deleting an occurrence → the labels are the output of the explicit tableau recursion extract, with one nonzero label per T/T† gate; reason: existence of some labels alone would drop the computation clause; nonidentity labels are the model's (Section 3.1)
--   - reading: U = F R_{ε_n}(P(p_n)) ⋯ R_{ε_1}(P(p_1)), global phases tracked or ignored consistently → U = u · F · R_{ε_n}(P(p_n)) ⋯ R_{ε_1}(P(p_1)) for some u with |u| = 1; reason: T and T† equal the rotations about Z only up to global phase (p.4)
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 4.1, Eq. (4), p.6

import Mathlib
import Definitions.Def_CutRankSched_Supplement_Gate
import Definitions.Def_CutRankSched_Supplement_Gate_IsT
import Definitions.Def_CutRankSched_Supplement_circuitUnitary
import Definitions.Def_CutRankSched_Supplement_traceUnitary
import Definitions.Def_CutRankSched_Supplement_IsClifford
import Definitions.Def_CutRankSched_Supplement_extract

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- **Theorem 4.1 (Exact signed Clifford-frame extraction)** (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 4.1, Eq. (4), p.6).
Every Clifford+T/T† circuit on `m` qubits has a representation
`U = F R_{ε_n}(P(p_n)) ⋯ R_{ε_1}(P(p_1))` (4), where `F` is Clifford and `n` is the number of
input `T`/`T†` occurrences. The signs and Pauli labels can be computed exactly by
Clifford-tableau updates without deleting an occurrence.

Stated for the labels `(ε_i, p_i)` produced by the tableau recursion `extract`: their number is the
number of `T`/`T†` gates, every `p_i` is nonzero, and (4) holds up to a global phase `u`, `|u| = 1`.

**Formalization Note** Gates act right to left (the first gate of the list acts first);
`R_ε(P) = exp(−iεπP/8)` in closed form; `P(p)` is the Hermitian representative `i^{x·z}X^xZ^z`. -/
theorem theorem_4_1 (m : ℕ) (c : List (Gate m)) :
    (extract c).length = c.countP Gate.IsT ∧ (∀ e ∈ extract c, e.2 ≠ 0) ∧
    ∃ (F : Op m) (u : ℂ), IsClifford F ∧ ‖u‖ = 1 ∧
      circuitUnitary c = u • (F * traceUnitary (extract c)) := by sorry

end Supplement

end CutRankSched
