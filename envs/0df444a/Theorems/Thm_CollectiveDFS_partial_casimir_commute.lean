-- Prove2me | Theorems.Thm_CollectiveDFS_partial_casimir_commute
-- name    : CollectiveDFS.partial_casimir_commute
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:03:03.116591+00:00
-- url     : https://prove2.me/theorems/e34b0b0c-e9f4-4d8e-a414-3fcec5db79c6
-- title:
--   (7.9), pp.23, 31 — the partial Casimirs commute
-- statement:
--   For $1\le k,l\le n$, the partial total angular momentum operators $(S^k)^2=\sum_{\alpha}(S^k_\alpha)^2$ commute:
--   $$\big[(S^k)^2,(S^l)^2\big]=0.$$
--
--   Their joint eigenvalues therefore label a basis of the $n$-qubit space, the path basis (7.11)–(7.12).
--
--   Differences from the source:
--   - encoding: qubits 1, …, n; |0⟩, |1⟩ → 0-based wires Fin n; Bool basis with false = |0⟩; reason: Lean convention; same operators
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, eqs. (7.8)–(7.9), p.23; Appendix A, p.31

import Mathlib
import Definitions.Def_CollectiveDFS_partialS

open QAlgorithms

namespace CollectiveDFS

/-- Eq. (7.9), proved in Appendix A (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, eqs. (7.8)–(7.9), p.23, and Appendix A, p.31, PDF
pp.23, 31): the partial total angular momentum operators `(S^k)² = Σ_α (S^k_α)²` commute,
`[(S^k)², (S^l)²] = 0` for all `k, l`.

**Formalization Note** Stated for the unnormalized `S^k_α = partialS n k α` of (7.7), as in (7.8);
`k, l` range over `1, …, n`. -/
theorem partial_casimir_commute (n k l : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hl : 1 ≤ l)
    (hln : l ≤ n) :
    Commute (∑ α : Fin 3, partialS n k α ^ 2) (∑ α : Fin 3, partialS n l α ^ 2) := by sorry

end CollectiveDFS
