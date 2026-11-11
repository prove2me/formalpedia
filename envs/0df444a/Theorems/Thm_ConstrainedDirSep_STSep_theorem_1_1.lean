-- Prove2me | Theorems.Thm_ConstrainedDirSep_STSep_theorem_1_1
-- name    : ConstrainedDirSep.STSep.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:06:41.843205+00:00
-- url     : https://prove2.me/theorems/4344fd0f-5d23-497e-ba9e-eb10470c7241
-- title:
--   Theorem 1.1 — hereditary directed s–t separators, feasible and minimum-weight, in 2^O(k⁴ log k) n^O(1) + 2^O(k²) τ_H(k)
-- statement:
--   There are a constant $C$ and two deterministic oracle Turing machines $M_1$ (unweighted) and $M_2$ (weighted) such that for every hereditary class $\mathcal H$ of digraphs (closed under isomorphism), every loopless digraph $D$ on $n$ vertices, all distinct terminals $s,t$ and every $k\ge0$, each run with the $\mathcal H$-membership oracle, the following hold, where $\log k=\log_2\max\{k,2\}$.
--
--   1. **Feasible separator.** On input $(D,s,t,k)$, $M_1$ halts within $C\cdot2^{Ck^4\log k}\cdot(n+1)^C$ steps (oracle calls at unit cost), makes at most $C\cdot2^{Ck^2}$ oracle calls, each about a digraph with at most $k$ vertices, and outputs an $s$–$t$ vertex separator $S$ with $|S|\le k$ and $D[S]\in\mathcal H$ (a feasible separator), or "none" exactly when no feasible separator exists.
--   2. **Minimum weight.** For every nonnegative integer weight function $w$ on $V(D)\setminus\{s,t\}$ given in binary, $M_2$ on input $(D,s,t,k,w)$ of total length $L$ satisfies the same bounds with $n$ replaced by $L$, and outputs a feasible separator of minimum weight $w(S)=\sum_{v\in S}w(v)$, or "none" exactly when no feasible separator exists.
--
--   Answering each oracle call by a membership algorithm for $\mathcal H$ of running time $\tau_{\mathcal H}(k)$ on adjacency matrices of digraphs with at most $k$ vertices gives the source's bound
--   $$2^{O(k^4\log k)}\,n^{O(1)}+2^{O(k^2)}\,\tau_{\mathcal H}(k).$$
--   Taking $\mathcal H$ to be the arcless digraphs gives the first FPT algorithm for Independent Directed $s$–$t$ Separator (Corollary 1.2), and the result extends the undirected theorem of Marx, O'Sullivan and Razgon to directed graphs.
--
--   Differences from the source:
--   - generalization: for each decidable hereditary H, an algorithm (which may embed a decider of H) with running time 2^{O(k⁴ log k)} n^{O(1)} + 2^{O(k²)} τ_H(k) → one constant and two oracle programs for every hereditary isomorphism-closed H, accessing H only through its membership oracle, with at most C·2^{C·k²} calls, each on a loopless digraph with at most k vertices, and at most C·2^{C·k⁴·⌊log₂ max(k,2)⌋}·(n + 1)^C steps in total, calls at unit cost; reason: replacing every call by a run of a decider of H on that digraph gives the source's bound, and decidability is then not needed.
--   - generalization: H a class of loopless digraphs → any isomorphism-closed hereditary predicate on digraphs on {0, …, m−1} (it may also contain digraphs with loops); reason: the oracle is asked only about loopless digraphs, and every class of the source is such a predicate.
--   - generalization: O(·) constants for a fixed H (p. 2: "The hereditary class … are fixed"), which may depend on H → one constant C chosen before H and the instance; reason: a constant uniform in H is in particular one for each fixed H, and the proof's constants do not depend on H (H enters only through the membership table).
--   - reading: unnamed machine model → a deterministic Mathlib multi-stack Turing machine (TM2) with the published oracle mechanism HMBinPacking.OracleMachine; reason: the bounds are polynomial in n for fixed k, the same in all polynomially equivalent deterministic models.
--   - encoding: 2^{O(k⁴ log k)} n^{O(1)} → C·2^{C·k⁴·⌊log₂ max(k, 2)⌋}·(n + 1)^C, with n the number of vertices (clause 1) and the input length (clause 2); reason: the floor changes log₂ by a factor at most 2 and n + 1 avoids 0^C, both absorbed in C; the meaning of n is the source's (p. 2).
--   - encoding: the input → adjacency matrix of D on {0, …, n − 1}, then s, t, k (and the weights of the nonterminals) in self-delimiting binary; the output → the bit 0 for "none", or the bit 1 followed by the n membership bits of S; reason: a standard binary encoding.
--   - encoding: w : V(D) \ {s, t} → ℤ≥0 → w : {0, …, n − 1} → ℕ whose values at s and t are neither encoded nor used; reason: separators never contain s or t.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), p. 2 (PDF 5), Theorem 1.1 (restated and proved p. 26, PDF 29; weighted clause Theorem 5.15, p. 27, PDF 30)

import Mathlib
import Definitions.Def_HMBinPacking_OracleMachine
import Definitions.Def_ConstrainedDirSep_STSep_Separator
import Definitions.Def_ConstrainedDirSep_STSep_Encoding
import Definitions.Def_ConstrainedDirSep_STSep_OracleRuns

namespace ConstrainedDirSep.STSep

/-- Olkowski, Ramanujan, *Constrained Directed Separation*, STOC 2027 submission (manuscript
sha256 4dd06c29…), p. 2 (PDF 5), Theorem 1.1 (proved p. 26, PDF 29; weighted clause Theorem 5.15):
for a decidable hereditary class `H`, an algorithm, given an instance of H-Directed s–t Separator,
runs in time `2^{O(k⁴ log k)} n^{O(1)} + 2^{O(k²)} τ_H(k)` and either outputs a feasible s–t
separator or correctly concludes that none exists; within the same time bound it computes a
minimum-weight feasible s–t separator given nonnegative vertex weights.

One constant `C` and two oracle programs (unweighted, weighted) serve every hereditary
isomorphism-closed class `H`, accessed only through its membership oracle: at most `C·2^{C k²}`
calls, each on a digraph with at most `k` vertices, and at most `C·2^{C k⁴ log k}·(n + 1)^C` steps
in total (calls at unit cost), where `n` is the number of vertices in the unweighted clause and the
input length in the weighted clause, and `log k = log₂ max{k, 2}`. -/
theorem theorem_1_1 :
    ∃ C : ℕ, ∃ OM₁ OM₂ : HMBinPacking.OracleMachine,
      (∀ H : DigraphClass, IsoClosed H → Hereditary H →
        ∀ (n : ℕ) (D : Digraph (Fin n)), Loopless D → ∀ s t : Fin n, s ≠ t → ∀ k : ℕ,
        ∃ out : List Bool,
          ORunsWithinCalls OM₁ (HOracle H) (encInstance D s t k) out
            (C * 2 ^ (C * k ^ 4 * Nat.log 2 (max k 2)) * (n + 1) ^ C)
            (C * 2 ^ (C * k ^ 2)) (IsSmallDigraphQuery k) ∧
          ((out = encNone ∧ ∀ S : Finset (Fin n), ¬ IsFeasible H D s t k S) ∨
            ∃ S : Finset (Fin n), out = encSet S ∧ IsFeasible H D s t k S)) ∧
      (∀ H : DigraphClass, IsoClosed H → Hereditary H →
        ∀ (n : ℕ) (D : Digraph (Fin n)), Loopless D → ∀ s t : Fin n, s ≠ t →
        ∀ (k : ℕ) (w : Fin n → ℕ),
        ∃ out : List Bool,
          ORunsWithinCalls OM₂ (HOracle H) (encWInstance D s t k w) out
            (C * 2 ^ (C * k ^ 4 * Nat.log 2 (max k 2)) * ((encWInstance D s t k w).length + 1) ^ C)
            (C * 2 ^ (C * k ^ 2)) (IsSmallDigraphQuery k) ∧
          ((out = encNone ∧ ∀ S : Finset (Fin n), ¬ IsFeasible H D s t k S) ∨
            ∃ S : Finset (Fin n), out = encSet S ∧ IsFeasible H D s t k S ∧
              ∀ S' : Finset (Fin n), IsFeasible H D s t k S' → wsum w S ≤ wsum w S')) := by sorry

end ConstrainedDirSep.STSep
