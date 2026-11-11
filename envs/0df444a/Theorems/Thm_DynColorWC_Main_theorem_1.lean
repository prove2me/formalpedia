-- Prove2me | Theorems.Thm_DynColorWC_Main_theorem_1
-- name    : DynColorWC.Main.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:47:25.343061+00:00
-- url     : https://prove2.me/theorems/63762a62-9cf6-4435-a5b5-f196ee1608fa
-- title:
--   Theorem 1 — an explicit proper (Δ+1)-coloring with polylog n worst-case update time and recourse, w.h.p. against an oblivious adversary
-- statement:
--   There is a randomized fully dynamic algorithm that explicitly maintains a proper $(\Delta+1)$-coloring of an $n$-vertex graph whose maximum degree always stays at most $\Delta$, against an oblivious adversary. Each edge insertion or deletion takes $\mathrm{polylog}\,n$ time and recolors at most $\mathrm{polylog}\,n$ vertices, with high probability — in the sense of Theorem 4: for any fixed $c,d>0$, simultaneously over any oblivious sequence of at most $n^d$ updates, with probability at least $1-1/n^c$.
--
--   In Lean: there are one program and one word-size constant such that for all $c,d>0$ there are $k,K$ with: for every $n\ge2$, every $\Delta$ and every legal update sequence $\sigma$ from the empty graph with $|\sigma|\le n^d$, fixed before the coin tape, the set of coin tapes on which preprocessing does not complete, or some update takes more than $K(\log_2n)^k$ steps, or recolors more than $K(\log_2n)^k$ vertices, or the coloring written by the machine is not a proper coloring with colors in $\{1,\dots,\Delta+1\}$ after preprocessing or after some update, has measure at most $n^{-c}$.
--
--   Differences from the source:
--
--   - encoding: machine model not specified (§3: set and map operations in O(log |S|) worst-case time, uniform random choices) → the published DynBrooks word RAM (unit-cost uniform random words, a read that blocks until an operation is delivered, every instruction one step) with word size a·⌈log₂(n+1)⌉, the program and a fixed before n, Δ and the sequence; reason: the standard word-RAM reading of §3; a blocking read gives per-update worst-case time and rules out look-ahead
--   - encoding: Δ, an upper bound on the maximum degree known to the algorithm → preprocessing receives the words n and min(Δ, n); reason: Δ may exceed every word; when Δ ≥ n every degree is below n and the colors 1, …, min(Δ,n)+1 lie in [Δ+1]
--   - encoding: the graph starts empty (§3) and undergoes legal edge updates (degree at most Δ at every moment) → IsLegalSeq Δ σ: from the empty graph on Fin n, each update inserts a non-edge uv (u ≠ v) or deletes an edge, and leaves every degree ≤ Δ; times 0, …, |σ| are the completed states after preprocessing and after each update; reason: §3 dynamic graphs model; no condition beyond the degree bound
--   - encoding: 'explicitly maintains a proper (Δ+1)-coloring'; 'recolors at most polylog n vertices' → the coloring is the machine's own change log: output words read as pairs (v, q) meaning χ(v) := q, applied in order to the all-1 coloring; the recourse of update t is the number of vertices whose color differs between the completed states before and after it; reason: explicit means the algorithm reports every change (§1.1 contrasts the implicit query model of [GK27]); writing a change costs machine steps
--   - encoding: 'with high probability' (Theorem 1), made precise by Theorem 4: for any fixed c, d > 0, simultaneously over any oblivious sequence of at most n^d updates, with probability at least 1 − 1/n^c → ∃ program ∀ c, d > 0 ∃ k, K: for every n ≥ 2, Δ and legal σ with |σ| ≤ n^d (fixed before the coin tape), the set of tapes on which some guarantee fails at some update has measure ≤ n^{−c}; reason: Theorem 4 (p. 49) restates Theorem 1 with these quantifiers; one failure event covers every update
--   - encoding: polylog n time and recourse → K·(log₂ n)^k with k, K chosen after c, d and before n, Δ and the sequence; n ≥ 2; reason: log is base 2 (§3); n ≤ 1 admits no edge update, and n ≥ 2 makes log₂ n ≥ 1
--   - encoding: Theorem 1 bounds the edge updates only → preprocessing (time not bounded) must reach a completed state, and the coloring after it (of the empty graph) must be proper; reason: the coloring is maintained from the start; without a completed preprocessing state no update is ever served
-- source:
--   Flin and Ghaffari (2026), Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case Update Time, STOC 2027 submission, supplied PDF sha256 93ebb2ffd4839b5e525b4550a6569cf5234550ee4a44351aedab3ea3154300e3, Theorem 1, p. 2 (PDF 4); Theorem 4, p. 49 (PDF 51)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynColorWC_Main_Model

namespace DynColorWC.Main

/-- **Theorem 1** (Flin and Ghaffari (2026), *Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case
Update Time*, STOC 2027 submission, sha256 93ebb2ff…3154300e3, p. 2 (PDF 4)), with "with high
probability" as made precise by its restatement **Theorem 4**, p. 49 (PDF 51).

There are one program `P` of the word RAM and one word-size constant `a` such that, for all
`c, d > 0`, there are `k` and `K` with the following property. For every `n ≥ 2`, every degree bound
`Δ`, and every legal update sequence `σ` from the empty graph on `Fin n` with at most `n^d` updates,
fixed before the coin tape (oblivious adversary), the coin tapes `ω` (word size `a·⌈log₂(n+1)⌉`) on
which some of the following fails have measure at most `n^{-c}`:
* preprocessing on the words `n, min Δ n` reaches a completed state;
* every update takes at most `K (log₂ n)^k` steps (worst case);
* every update recolors at most `K (log₂ n)^k` vertices of the coloring the machine writes;
* after preprocessing and after every update, the written coloring is a proper coloring of the
  current graph with colors in `{1, …, Δ+1}`. -/
theorem theorem_1 :
    ∃ (P : DynBrooks.Program) (a : ℕ),
      ∀ c d : ℝ, 0 < c → 0 < d →
        ∃ (k : ℕ) (K : ℝ),
          ∀ (n Δ : ℕ), 2 ≤ n →
            ∀ σ : List (DynBrooks.Update n), IsLegalSeq Δ σ → (σ.length : ℝ) ≤ (n : ℝ) ^ d →
              DynBrooks.coinMeasure (wordSize a n)
                {ω | (stateAt P ω [n, min Δ n] σ 0).isNone ∨
                  (∃ t < σ.length,
                    ¬ TimeLE (updateTime P ω [n, min Δ n] σ t) (K * Real.logb 2 n ^ k) ∨
                    K * Real.logb 2 n ^ k <
                      (recolored (colorAt P ω [n, min Δ n] σ t)
                        (colorAt P ω [n, min Δ n] σ (t + 1)) : ℝ)) ∨
                  (∃ t ≤ σ.length,
                    ¬ IsProperDeltaPlusOne Δ (graphAt σ t) (colorAt P ω [n, min Δ n] σ t))}
                ≤ ENNReal.ofReal ((n : ℝ) ^ (-c)) := by sorry

end DynColorWC.Main
