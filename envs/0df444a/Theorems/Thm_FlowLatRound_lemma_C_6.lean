-- Prove2me | Theorems.Thm_FlowLatRound_lemma_C_6
-- name    : FlowLatRound.lemma_C_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:59:39.322199+00:00
-- url     : https://prove2.me/theorems/b3482ef5-323c-41c9-b251-729a387575ab
-- title:
--   Lemma C.6 — exact sampling of (P1)–(P3) in expected polynomial time; slot sequences decoded as Prüfer codes give $P[T]\propto w(T)$
-- statement:
--   For every degree sequence $g$ with $n\ge2$ and cycle rank $d\ge1$:
--
--   1. the program `sampleProcess` (slots and Prüfer decoding for (P1), uniform attachments for (P2), a uniform matching for (P3)), run on fair bits, halts with probability $1$, outputs each pair $(\pi,T)$ with exactly its probability in the process (P1)–(P3), and its expected bit cost is at most $c\,(\sum_ig_i)^k$, with constants $c,k$ independent of $g$;
--   2. choosing an ordered sequence of $n-2$ distinct slots uniformly at random (each of the $(\alpha)_{n-2}$ sequences equally likely) and decoding its vertex labels as a Prüfer code produces each labeled tree $t$ with probability $w(t)/\sum_{t'}w(t')$.
--
--   This is what makes the random lattice of Theorem 1.1 samplable.
--
--   Differences from the source:
--   - encoding: (expected) polynomial time in the model of Appendix B (exact rational arithmetic, rejection sampling, expectation over the random choices) → a bit-cost counter (each operation charged (ratBits a + ratBits b + 1)^2, coin reads and list/array steps 1), a fair-coin tape with fuel-indexed halting, non-halting runs charged ⊤, expectation as ∫⁻ over the tape; polynomial = ∃ c k, one pair for all inputs; reason: a faithful rendering of Appendix B; the programs are named so the claim is about them
--   - generalization: the process can be simulated exactly in expected polynomial time → the named program sampleProcess (the proof's simulation) is exact and runs in expected time ≤ c·(Σ g_i)^k; reason: a specific program with these properties implies the existence claim
--   - reading: order of the uniform choices of (P2) and (P3) not fixed → vertices in order, tree edges in the decoder's order; (P3) pairs the least unmatched half-edge with a uniform other one; reason: any order gives the uniform injection and the uniform perfect matching; one order must be fixed to name a program
--   - reading: the process (P1)–(P3) with degrees (g_i) (no restriction written in the statement) → 2 ≤ n and 1 ≤ d as hypotheses; reason: Appendix C.4 defines the tilted model with degrees (g_i) for n ≥ 2 and d ≥ 1 (p.26); this is the standing setting of the statement
--   - encoding: the tilted configuration model (P1)–(P3); edges of G(π) labeled by the pairs of π → processProb: the step probabilities of (P1)–(P3) summed over the outcomes producing (π, T); edges of G(π) enumerated by their smaller half-edge and oriented from it (pairLaw = marginal of π); reason: the law of the process itself; a relabeling or reorientation of edges is a signed coordinate permutation and changes no lattice, cell, τ or cycle length
--   - encoding: vertices [n] and edges labeled 1..m → Fin n and Fin m (0-indexed); reason: Lean convention; relabeling changes no instance
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), Lemma C.6, p.26 (PDF 28)

import Mathlib
import Definitions.Def_FlowLatRound_Sampler

namespace FlowLatRound

open MeasureTheory
open scoped ENNReal

/-- Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027 submission,
sha256 35bd3e4b…aeac), Lemma C.6, p.26 (PDF 28). Exact sampling, for every degree sequence `(gᵢ)` with
`n ≥ 2` and cycle rank `d ≥ 1`:
1. the program `sampleProcess g` (slots + Prüfer decoding for (P1), uniform attachments for
   (P2), uniform matching for (P3)), run on fair bits, halts almost surely, outputs `(π, T)` with
   exactly the probability `processProb g π T` of the process (P1)–(P3), and has expected cost at
   most `c (Σ gᵢ)^k`, with one `(c, k)` for all degree sequences;
2. choosing an ordered sequence of `n − 2` distinct slots uniformly at random and decoding its
   vertex labels as a Prüfer code produces each labeled tree `t` with probability
   `w(t)/Σ w` (= `p₁(t)`).

**Formalization Note.** "Expected polynomial time" is the lower Lebesgue integral of the bit cost
(`⊤` on non-halting tapes) under the fair-coin tape, bounded by `c·(Σ gᵢ)^k` (`Σ gᵢ = 2m`). The
pairing is output as its map on half-edges. A uniform ordered sequence of distinct slots has
probability `1/(α)_{n−2}` each. -/
theorem lemma_C_6 :
    (∃ c k : ℕ, ∀ (n : ℕ) (g : DegSeq n), 2 ≤ n → 1 ≤ g.cr →
      tape {ω | ¬ halts g.sampleProcess ω} = 0 ∧
      (∀ (π : g.Pairing) (T : Finset (Fin g.m)),
        tape {ω | outputOf g.sampleProcess ω = some (⇑π.1, T)} =
          ENNReal.ofReal (g.processProb π T)) ∧
      ∫⁻ ω, costOf g.sampleProcess ω ∂tape ≤ (c : ℝ≥0∞) * ((∑ i, g.g i : ℕ) : ℝ≥0∞) ^ k) ∧
    (∀ (n : ℕ) (g : DegSeq n), 2 ≤ n → 1 ≤ g.cr → ∀ t : LTree n,
      ((Finset.univ.filter (fun s : Fin (n - 2) → g.Slot =>
          Function.Injective s ∧ pruferTree n (List.ofFn (fun j => (s j).1)) = t.1)).card : ℝ) /
        (g.alpha.descFactorial (n - 2) : ℝ) = g.p1 t) := by sorry

end FlowLatRound
