-- Prove2me | Theorems.Thm_ExtensionComplexity_TSP_Supplement_quantum_classical_separation
-- name    : ExtensionComplexity.TSP.Supplement.quantum_classical_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:39:26.721288+00:00
-- url     : https://prove2.me/theorems/6d248588-2ac4-43ca-8d1d-56e6824d2dbe
-- title:
--   Theorem 18 — exponential separation of quantum and classical communication in expectation
-- statement:
--   For every $n\ge1$ there is a nonnegative real matrix $M$ whose rows and columns are indexed by the $2^n$ strings in $\{0,1\}^n$ such that $M$ is computed in expectation by a one-way quantum protocol using $\log_2 n+O(1)$ qubits, while every classical private-coin randomized protocol with nonnegative outputs computing $M$ in expectation communicates $\Omega(n)$ bits. Explicitly, there are constants $C_1\in\mathbb R$, $C_2>0$ and $N$ such that for all $n\ge1$ there exists such an $M$ with
--
--   $$
--   \exists k\le \log_2 n+C_1:\ \mathcal Q_{2^k}(M),\qquad
--   n\ge N\ \Longrightarrow\ \operatorname{cost}(P)\ge C_2\,n\ \text{ for every classical }P\text{ computing }M\text{ in expectation},
--   $$
--
--   where $\mathcal Q_{2^k}(M)$ means that a one-way quantum protocol with $2^k$-dimensional (that is, $k$-qubit) messages computes $M$ in expectation.
--
--   This is the paper's exponential separation between quantum and classical communication in expectation, the protocol form of the gap between PSD rank and nonnegative rank. It is a companion theorem of the mission's goal, not a step of its proof.
--
--   **Formalization Note** The constants of $O(1)$ and $\Omega(n)$ are uniform in $n$ and quantified before $n$. The logarithm is base 2, the paper's convention for counting qubits (a $k$-qubit state has dimension $2^k$, p. 17:16; Corollary 15 counts $\lceil\log(r+1)\rceil$ qubits for $(r+1)$-dimensional messages). The guard $n\ge1$ only excludes $n=0$, where $\log n$ is undefined.
--
--   Differences from the source:
--   - encoding: 2^n×2^n matrices → Matrix (Fin n → Bool) (Fin n → Bool) ℝ; reason: the paper indexes rows and columns by n-bit strings, and the statement is an existence claim invariant under reindexing
--   - encoding: quantum protocol using log n + O(1) qubits → a OneWayProtocol with message dimension 2^k and k ≤ log₂ n + C₁; reason: §4 defines only one-way quantum protocols, and a k-qubit state is a state of dimension 2^k (p. 17:16)
--   - reading: any classical randomized protocol → every ClassicalProtocol (private-coin binary protocol tree, nonnegative outputs by either party, cost = depth); reason: the paper cites the model of Faenza et al. (2011) without defining it; its proof uses private randomness, and with public coins the claim would be false; multi-round protocols are included, so every one-way protocol is covered
--   - reading: for each n → n ≥ 1; reason: log n + O(1) is undefined at n = 0
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, DOI 10.1145/2716307, p. 17:19, Theorem 18

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_Supplement_OneWayProtocol
import Definitions.Def_ExtensionComplexity_TSP_Supplement_ClassicalProtocol

namespace ExtensionComplexity.TSP.Supplement

/-- Theorem 18, p. 17:19: rows and columns are indexed by `n`-bit strings (`2^n × 2^n`); a
`k`-qubit message is a state of dimension `2^k` (p. 17:16). The `O(1)` and `Ω(n)` constants are
uniform in `n`; the classical clause quantifies over every private-coin protocol. -/
theorem quantum_classical_separation :
    ∃ C₁ : ℝ, ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ N : ℕ, ∀ n : ℕ, 1 ≤ n →
      ∃ M : Matrix (Fin n → Bool) (Fin n → Bool) ℝ, (∀ a b, 0 ≤ M a b) ∧
        (∃ k : ℕ, (k : ℝ) ≤ Real.logb 2 n + C₁ ∧
          ∃ P : OneWayProtocol (Fin n → Bool) (Fin n → Bool) (2 ^ k), P.Computes M) ∧
        (N ≤ n → ∀ P : ClassicalProtocol (Fin n → Bool) (Fin n → Bool),
          P.Computes M → C₂ * n ≤ P.cost) := by sorry

end ExtensionComplexity.TSP.Supplement
