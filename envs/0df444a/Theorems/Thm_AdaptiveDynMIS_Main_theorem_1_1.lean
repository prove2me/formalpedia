-- Prove2me | Theorems.Thm_AdaptiveDynMIS_Main_theorem_1_1
-- name    : AdaptiveDynMIS.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:55:46.312504+00:00
-- url     : https://prove2.me/theorems/dff76959-d934-46c3-b623-9eb7befa31e3
-- title:
--   Theorem 1.1 — a randomized fully dynamic MIS with Õ(m^{5/8}) amortized update time against adaptive adversaries
-- statement:
--   Let $G=(V,E)$ be an initially empty undirected graph on $n$ vertices that undergoes edge insertions and deletions, with at most $m$ edges at any time. There is a randomized algorithm that maintains a maximal independent set of $G$ against adaptive adversaries with amortized update time $\tilde O(m^{5/8})=\tilde O(m^{2/3-1/24})$.
--
--   Precisely: for all $c,d>0$ there are a word-RAM program $P$, a word-size constant $a$ and constants $K$, $k$ such that for every $n\ge2$, every $m\ge1$ and every deterministic adaptive adversary $A$ (which sees only the reported sets and proposes legal updates, at most $\lfloor n^d\rfloor$ of them), writing $\sigma(\omega)$ for the realized update sequence on the coin tape $\omega$ and $M_t$, $G_t$ for the reported set and the graph after $t$ updates:
--
--   1. on **every** coin tape, after preprocessing and after every completed update $t\le|\sigma(\omega)|$, $M_t$ is a maximal independent set of $G_t$;
--   2. the coin tapes on which preprocessing takes more than $K\,n\,(\log_2 n)^k$ steps, or a delivered update does not complete, or for some $t\le|\sigma(\omega)|$
--   $$\sum_{s<t}\mathrm{time}(\text{update } s)\ >\ K\,t\,m^{5/8}(\log_2 n)^k,$$
--   have probability at most $n^{-c}$.
--
--   This is the paper's main result, the first polynomial improvement over the $O(m^{2/3})$ bound of Gupta and Khan against adaptive adversaries.
--
--   **Formalization Note.** The model is the definition `Model`: the published word RAM with words of $a\lceil\log_2(n+1)\rceil$ bits and unit-cost random words; the input words $n$ and $\min(m,n^2)$; the reported MIS read from the machine's own output pairs, starting from $V$; an illegal proposal ends the interaction. An MIS is the published `SmoothedMIS.IsMIS` (independent, and every vertex is in the set or adjacent to it).
--
--   Differences from the source:
--   - encoding: "a randomized algorithm" (no machine named) → a program of the published word RAM with words of $a\lceil\log_2(n+1)\rceil$ bits and unit-cost uniform random words, input words $n$ and $\min(m,n^2)$; reason: the word RAM with $O(\log n)$-bit words and random bits implicit in §3 ($m$ may exceed every word)
--   - encoding: "maintains a maximal independent set" → the machine writes (vertex, bit) pairs, the reported set is $V$ with the pairs applied in order, and it is an MIS of the current graph on every coin tape after preprocessing and after every completed update; reason: the paper reports the changes of an explicit $M$, starting from $M=V$, and its correctness holds on every realization (p. 35)
--   - encoding: "against adaptive adversaries" → every deterministic strategy mapping the list of reported sets to the next update or stop; reason: the adversary sees only the reported MISs (p. 5, p. 35), and a randomized adversary is a mixture of deterministic ones
--   - encoding: "at most $m$ edges at any time" → a proposal is delivered only if the graph after it has at most $m$ edges, otherwise the interaction ends; reason: legality is a promise on the adversary
--   - encoding: $n$ vertices $V$, any $n$ and $m$ → vertices `Fin n`, $n\ge2$, $m\ge1$; reason: at $n=1$ there is no edge to update and $(\log_2 n)^k=0$ leaves $\tilde O$ meaningless; at $m=0$ no insertion is legal
--   - reading: "with high probability", "polynomial-length update sequence" → for all $c,d>0$ there are $P,a,K,k$ with failure probability at most $n^{-c}$ over at most $\lfloor n^d\rfloor$ updates; reason: the definition on p. 5 ("constants in the algorithm chosen accordingly")
--   - reading: amortized update time $\tilde O(m^{5/8})$ → for every prefix $t$, the total time of updates $1..t$ is at most $K\,t\,m^{5/8}(\log_2 n)^k$, every delivered update completes, and preprocessing takes at most $K\,n(\log_2 n)^k$ steps, all outside an event of probability $\le n^{-c}$; reason: $\tilde O$ suppresses factors polynomial in $\log n$ (footnote 1); amortized means a bound on every prefix; the theorem states no preprocessing bound, and the paper's $O(n)$ initialization (p. 35) is within this one
-- source:
--   Chen, Fan, Zhang, Faster Dynamic Maximal Independent Set against Adaptive Adversaries, arXiv:2611.05932 (PDF sha256 a65b11d9…ec4a), p. 2, Theorem 1.1 (with p. 5, §2, for 'with high probability' and the adversary)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_SmoothedMIS_IsMIS
import Definitions.Def_AdaptiveDynMIS_Main_Model

namespace AdaptiveDynMIS.Main

/-- **Theorem 1.1** (Chen, Fan, Zhang, *Faster Dynamic Maximal Independent Set against Adaptive
Adversaries*, arXiv:2611.05932 (PDF sha256 a65b11d9…ec4a), p. 2 (PDF 4)), with "with high
probability" and "adaptive adversary" as made precise on p. 5 (PDF 7).

For all `c, d > 0` there are a word-RAM program `P`, a word-size constant `a` and constants `k`, `K`
such that for every `n ≥ 2`, every edge bound `m ≥ 1` and every deterministic adaptive adversary `A`
(which sees only the reported sets and proposes at most `⌊n^d⌋` updates, each legal for `m`), with
`σ(ω)` the realized update sequence on coin tape `ω` (word size `a·⌈log₂(n+1)⌉`):
* on **every** tape, after preprocessing and after every completed update, the reported set is a
  maximal independent set of the current graph;
* the tapes on which preprocessing takes more than `K·n·(log₂ n)^k` steps, or a delivered update does
  not complete, or the first `t` updates take more than `K·t·m^{5/8}·(log₂ n)^k` steps in total for
  some `t`, have measure at most `n^{-c}`. -/
theorem theorem_1_1 :
    ∀ c d : ℝ, 0 < c → 0 < d →
      ∃ (P : DynBrooks.Program) (a k : ℕ) (K : ℝ),
        ∀ (n m : ℕ), 2 ≤ n → 1 ≤ m → ∀ A : Strategy n,
          (∀ (ω : ℕ → BitVec (wordSize a n)) (t : ℕ), t ≤ (realized P a d n m A ω).length →
            (stateAt P ω (initWords n m) (realized P a d n m A ω) t).isSome →
            SmoothedMIS.IsMIS (graphAt (realized P a d n m A ω) t)
              ↑(reportedAt P ω (initWords n m) (realized P a d n m A ω) t)) ∧
          DynBrooks.coinMeasure (wordSize a n)
            {ω | ¬ TimeLE (DynBrooks.time P ω (initConfig (wordSize a n) (initWords n m)))
                    (K * n * Real.logb 2 n ^ k) ∨
              (∃ t < (realized P a d n m A ω).length,
                (stateAt P ω (initWords n m) (realized P a d n m A ω) (t + 1)).isNone) ∨
              (∃ t ≤ (realized P a d n m A ω).length,
                ¬ TimeLE (totalUpdateTime P ω (initWords n m) (realized P a d n m A ω) t)
                  (K * t * (m : ℝ) ^ ((5 : ℝ) / 8) * Real.logb 2 n ^ k))}
            ≤ ENNReal.ofReal ((n : ℝ) ^ (-c)) := by sorry

end AdaptiveDynMIS.Main
