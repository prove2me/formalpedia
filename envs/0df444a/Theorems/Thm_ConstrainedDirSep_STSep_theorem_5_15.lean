-- Prove2me | Theorems.Thm_ConstrainedDirSep_STSep_theorem_5_15
-- name    : ConstrainedDirSep.STSep.theorem_5_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:06:50.20626+00:00
-- url     : https://prove2.me/theorems/78660770-7f8a-4935-a5a9-c42292413956
-- title:
--   Theorem 5.15 — minimum-weight hereditary directed s–t separator in 2^O(k⁴ log k) n^O(1) + 2^O(k²) τ_H(k), n the input length
-- statement:
--   There are a constant $C$ and a deterministic oracle Turing machine $M$ such that for every hereditary class $\mathcal H$ of digraphs (closed under isomorphism), every loopless digraph $D$ on $\{0,\dots,n_D-1\}$, distinct terminals $s,t$, every $k\ge0$ and every nonnegative integer weight function $w$ on $V(D)\setminus\{s,t\}$ given in binary: $M$, run with the $\mathcal H$-membership oracle on the input $(D,s,t,k,w)$ of length $n$, halts within
--   $$C\cdot2^{C k^4\log k}\cdot(n+1)^C$$
--   steps (oracle calls at unit cost), makes at most $C\cdot2^{Ck^2}$ oracle calls, each about a digraph with at most $k$ vertices, and outputs an $s$–$t$ vertex separator $S$ of minimum weight $w(S)$ among those with $|S|\le k$ and $D[S]\in\mathcal H$, or "none" exactly when no such separator exists. Here $\log k=\log_2\max\{k,2\}$.
--
--   Answering each oracle call by a membership algorithm for $\mathcal H$ of running time $\tau_{\mathcal H}(k)$ on digraphs with at most $k$ vertices gives the running time $2^{O(k^4\log k)}n^{O(1)}+2^{O(k^2)}\tau_{\mathcal H}(k)$ of the source. This is the weighted clause of Theorem 1.1.
--
--   Differences from the source:
--   - generalization: for each decidable hereditary H, an algorithm (which may embed a decider of H) with running time 2^{O(k⁴ log k)} n^{O(1)} + 2^{O(k²)} τ_H(k) → one oracle program for every hereditary isomorphism-closed H, accessing H only through its membership oracle, with at most C·2^{C·k²} calls, each on a loopless digraph with at most k vertices, and at most C·2^{C·k⁴·⌊log₂ max(k,2)⌋}·(n + 1)^C steps in total, calls at unit cost; reason: replacing every call by a run of a decider of H on that digraph gives the source's bound, and decidability is then not needed.
--   - generalization: H a class of loopless digraphs → any isomorphism-closed hereditary predicate on digraphs on {0, …, m−1} (it may also contain digraphs with loops); reason: the oracle is asked only about loopless digraphs, and every class of the source is such a predicate.
--   - generalization: O(·) constants for a fixed H (p. 2: "The hereditary class … are fixed"), which may depend on H → one constant C chosen before H and the instance; reason: a constant uniform in H is in particular one for each fixed H, and the proof's constants do not depend on H (H enters only through the membership table).
--   - reading: unnamed machine model → a deterministic Mathlib multi-stack Turing machine (TM2) with the published oracle mechanism HMBinPacking.OracleMachine; reason: the bounds are polynomial in n for fixed k, the same in all polynomially equivalent deterministic models.
--   - encoding: 2^{O(k⁴ log k)} n^{O(1)} → C·2^{C·k⁴·⌊log₂ max(k, 2)⌋}·(n + 1)^C; reason: the floor changes log₂ by a factor at most 2 and n + 1 avoids 0^C, both absorbed in C.
--   - encoding: the input → adjacency matrix of D on {0, …, n_D − 1}, then s, t, k and the weights of the nonterminals in self-delimiting binary; the output → the bit 0 for "none", or the bit 1 followed by the n_D membership bits of S; reason: a standard binary encoding; n is its length, as the source prescribes.
--   - encoding: w : V(D) \ {s, t} → ℤ≥0 → w : {0, …, n_D − 1} → ℕ whose values at s and t are neither encoded nor used; reason: separators never contain s or t.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), p. 27 (PDF 30), Theorem 5.15

import Mathlib
import Definitions.Def_HMBinPacking_OracleMachine
import Definitions.Def_ConstrainedDirSep_STSep_Separator
import Definitions.Def_ConstrainedDirSep_STSep_Encoding
import Definitions.Def_ConstrainedDirSep_STSep_OracleRuns

namespace ConstrainedDirSep.STSep

/-- Olkowski, Ramanujan, *Constrained Directed Separation*, STOC 2027 submission (manuscript
sha256 4dd06c29…), p. 27 (PDF 30), Theorem 5.15: for every decidable hereditary class `H`, an
algorithm, given `D`, terminals `s`, `t`, nonnegative integer weights on `V(D) \ {s, t}` and
`k ≥ 0`, runs in time `2^{O(k⁴ log k)} n^{O(1)} + 2^{O(k²)} τ_H(k)` (`n` the input-encoding length)
and computes a minimum-weight s–t separator among those with `|S| ≤ k` and `D[S] ∈ H`, or
determines that none exists.

One oracle program and one constant `C` serve every hereditary isomorphism-closed class `H`, which
is accessed only through its membership oracle: at most `C·2^{C k²}` calls, each on a digraph with
at most `k` vertices, and at most `C·2^{C k⁴ log k}·(n + 1)^C` steps in total (calls at unit cost). -/
theorem theorem_5_15 :
    ∃ C : ℕ, ∃ OM : HMBinPacking.OracleMachine,
      ∀ H : DigraphClass, IsoClosed H → Hereditary H →
      ∀ (n : ℕ) (D : Digraph (Fin n)), Loopless D → ∀ s t : Fin n, s ≠ t →
      ∀ (k : ℕ) (w : Fin n → ℕ),
      ∃ out : List Bool,
        ORunsWithinCalls OM (HOracle H) (encWInstance D s t k w) out
          (C * 2 ^ (C * k ^ 4 * Nat.log 2 (max k 2)) * ((encWInstance D s t k w).length + 1) ^ C)
          (C * 2 ^ (C * k ^ 2)) (IsSmallDigraphQuery k) ∧
        ((out = encNone ∧ ∀ S : Finset (Fin n), ¬ IsFeasible H D s t k S) ∨
          ∃ S : Finset (Fin n), out = encSet S ∧ IsFeasible H D s t k S ∧
            ∀ S' : Finset (Fin n), IsFeasible H D s t k S' → wsum w S ≤ wsum w S') := by sorry

end ConstrainedDirSep.STSep
