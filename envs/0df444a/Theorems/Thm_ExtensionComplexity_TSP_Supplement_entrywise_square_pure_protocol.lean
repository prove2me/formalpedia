-- Prove2me | Theorems.Thm_ExtensionComplexity_TSP_Supplement_entrywise_square_pure_protocol
-- name    : ExtensionComplexity.TSP.Supplement.entrywise_square_pure_protocol
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:37:47.01254+00:00
-- url     : https://prove2.me/theorems/01f27df9-ab33-4062-a98d-59b36ed46ebe
-- title:
--   Theorem 16 — pure-state protocol for an entrywise square
-- statement:
--   Let $M$ and $N$ be real matrices on the same arbitrary finite row and column sets. Assume $M$ has nonnegative entries, $N$ has ordinary matrix rank $r$, and $M_{ij}=N_{ij}^2$ for every entry. There exists a one-way quantum protocol with $(r+1)$-dimensional pure-state messages computing $M$ in expectation:
--
--   $$
--   \exists\,(\rho_i,E^j_o,\theta^j_o),\qquad
--   \operatorname{Pure}(\rho_i)\ \text{for every }i,\qquad
--   \sum_o\theta^j_o\operatorname{Tr}(E^j_o\rho_i)=M_{ij}\ \text{for every }i,j.
--   $$
--
--   The labels are nonnegative and the states and effects satisfy the normalization and positivity requirements of the protocol model. This companion theorem bounds quantum message dimension in terms of the rank of an entrywise square root, while retaining pure messages.
--
--   **Formalization Note** Rank zero and empty matrices are included. The square is entrywise, not a matrix product; the purity clause is retained in addition to the computation clause.
--
--   Differences from the source:
--   - encoding: finite real m-by-n matrices → Matrix ι κ ℝ with Fintype ι and Fintype κ, including empty index types; reason: a finite enumeration identifies these with the source matrices; no input size is excluded
--   - encoding: real states and finite POVMs with nonnegative real outputs → OneWayProtocol with PSD trace-one states, finite enumerated POVMs, nonnegative labels and the explicit Born expectation; reason: §4 and §4.2 define precisely these protocols; repeated labels can be merged without changing the reported-output distribution
--   - encoding: rank-r N and pure (r+1)-dimensional messages → Matrix.rank N = r and every density matrix is φφᵀ for a real vector with sum of squared coordinates equal to one; reason: ordinary rank and Euclidean unit vectors are the source conventions; purity is not replaced by arbitrary mixed states
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, DOI 10.1145/2716307, p. 17:18, Theorem 16

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_Supplement_OneWayProtocol

namespace ExtensionComplexity.TSP.Supplement

/-- Theorem 16, p. 17:18: the square is entrywise and every message is pure.
The zero-rank and empty-matrix cases are included. -/
theorem entrywise_square_pure_protocol {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M N : Matrix ι κ ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (r : ℕ) (hRank : Matrix.rank N = r) (hSquare : ∀ i j, M i j = (N i j) ^ 2) :
    ∃ P : OneWayProtocol ι κ (r + 1), P.Computes M ∧ P.PureMessages := by sorry

end ExtensionComplexity.TSP.Supplement
