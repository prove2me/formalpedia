-- Prove2me | Theorems.Thm_ExtensionComplexity_TSP_Supplement_protocol_psd_factorization
-- name    : ExtensionComplexity.TSP.Supplement.protocol_psd_factorization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:36:44.3053+00:00
-- url     : https://prove2.me/theorems/4469bbb1-6715-4291-acde-604049acd4c0
-- title:
--   Theorem 14 — quantum protocols and PSD factorizations (both parts)
-- statement:
--   Let $M$ be any finite matrix with nonnegative real entries, and let $r\in\mathbb N$. Write $\mathcal Q_r(M)$ for the existence of a one-way quantum protocol with $r$-dimensional messages computing $M$ in expectation, and $\mathcal F_r(M)$ for a PSD factorization by real $r\times r$ symmetric positive semidefinite matrices, with $\operatorname{Tr}(T_iU^j)=M_{ij}$. Then both implications hold:
--
--   $$
--   \mathcal Q_r(M)\Longrightarrow\mathcal F_r(M),\qquad
--   \mathcal F_r(M)\Longrightarrow\mathcal Q_{r+1}(M).
--   $$
--
--   This is the two-part connection between quantum communication in expectation and PSD factorization size. It is a companion theorem to the mission's extension-complexity goal, rather than a step in its proof.
--
--   **Formalization Note** No positive-rank, nonzero-factor, or nonempty-index premise is added. The zero normalizers appearing in the printed proof require case handling in a proof, rather than a restriction of the theorem.
--
--   Differences from the source:
--   - encoding: finite real m-by-n matrices → Matrix ι κ ℝ with Fintype ι and Fintype κ, including empty index types; reason: a finite enumeration identifies these with the source matrices; no input size is excluded
--   - encoding: real states and finite POVMs with nonnegative real outputs → OneWayProtocol with PSD trace-one states, finite enumerated POVMs, nonnegative labels and the explicit Born expectation; reason: §4 and §4.2 define precisely these protocols; repeated labels can be merged without changing the reported-output distribution
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, DOI 10.1145/2716307, p. 17:17, Theorem 14

import Mathlib
import Definitions.Def_ConeLifts_StableSet_HasPSDFactorization
import Definitions.Def_ExtensionComplexity_TSP_Supplement_OneWayProtocol

namespace ExtensionComplexity.TSP.Supplement

/-- Theorem 14, p. 17:17, both clauses with their printed message dimensions.
No nonzero-factor or positive-rank assumption is imposed. -/
theorem protocol_psd_factorization {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) (hM : ∀ i j, 0 ≤ M i j) (r : ℕ) :
    ((∃ P : OneWayProtocol ι κ r, P.Computes M) →
      ConeLifts.StableSet.HasPSDFactorization r M) ∧
    (ConeLifts.StableSet.HasPSDFactorization r M →
      ∃ P : OneWayProtocol ι κ (r + 1), P.Computes M) := by sorry

end ExtensionComplexity.TSP.Supplement
