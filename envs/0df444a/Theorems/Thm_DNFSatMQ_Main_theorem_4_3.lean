-- Prove2me | Theorems.Thm_DNFSatMQ_Main_theorem_4_3
-- name    : DNFSatMQ.Main.theorem_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:34:18.471704+00:00
-- url     : https://prove2.me/theorems/aa9d7dcf-92a9-42b9-960b-8bea23427b77
-- title:
--   Theorem 4.3 — a densifier and a uniform-distribution learner give an algorithm for Problem 1.1
-- statement:
--   Suppose $A_{den}$ is a $\gamma$-densifier (Definition 4.1) running in time $T_{den}(n,s,1/\varepsilon,1/\delta)$, outputting at most $\mathrm{poly}(n,s,1/\varepsilon,\log(1/\delta))$ conjunctions, with $1/\gamma(n,s,1/\varepsilon,1/\delta) = \mathrm{poly}(n,s,1/\varepsilon,\log(1/\delta))$; and $A_{learn}$ is a uniform-distribution learner (Definition 4.2) with learning time $T_{learn}(n,s,1/\varepsilon,1/\delta)$ and output size at most $S_{learn}(n,s,1/\varepsilon,1/\delta)$ on targets with at most $n$ variables. Then there is an algorithm $A$ that solves Problem 1.1 and outputs an explicitly represented hypothesis $h$ with a sampling procedure; its learning time is polynomial in
--   $$n,\ s,\ 1/\varepsilon,\ T_{den}(n,s,4/\varepsilon,4),\ T_{learn}(n,s,P,P),\ S_{learn}(n,s,P,P),$$
--   and the time per sample is $\mathrm{poly}(n,s,1/\varepsilon)\,S_{learn}(n,s,P,P)$, where $P = \mathrm{poly}(n,s,1/\varepsilon)$.
--
--   In Lean: given the two programs, arbitrary bound functions, with the learner bounds applying to every target dimension d ≤ n and the hypotheses, there are a learner program, a sampler program and $c\in\mathbb N$ such that, with $P = c(n+s+1/\varepsilon)^c$, every instance satisfies `SolvesP11` for circuit hypotheses with learning time $\lceil c(n+s+1/\varepsilon+T_{den}(n,s,4/\varepsilon,4)+T_{learn}(n,s,P,P)+S_{learn}(n,s,P,P))^c\rceil$, $\lceil P\rceil$ sampler random bits and sampler time $\lceil P\cdot S_{learn}(n,s,P,P)\rceil$.
--
--   Differences from the source:
--   - encoding: coordinates [n] = {1, …, n} and bits {0, 1} → `Fin n` (coordinates 0, …, n−1) and `Bool`; reason: Lean convention; same instances
--   - encoding: randomized algorithms with time bounds; poly(·) → programs of the fair-coin RAM; guarantees of A_den, A_learn hold for every coin-tape length L ≥ ⌈T⌉; poly as c·(n + s + 1/ε + log(1/δ))^c; reason: a randomized algorithm has an unbounded supply of coins; polynomial bounds take this form for n, s ≥ 1
--   - encoding: "outputs at most poly(…) conjunctions" → every output word that decodes to a list of conjunctions has at most that many; reason: the bound holds on every run
--   - generalization: ε, δ given to the algorithms → ε, δ any reals, accessed by comparison queries (`dnfOracle`); reason: covers every rational encoding; the time bounds do not depend on the encoding
--   - encoding: explicitly represented hypothesis (bounded-fan-in evaluation circuit, p. 10) → the output word starts with a circuit (`circuitHyp`) whose size is at most the learning-time bound; reason: the clause adds nothing: a decoded circuit with k gates occupies more than k output bits, and each output bit costs a step
--   - encoding: the sampler uses poly(n, s, 1/ε) random bits and runs in the stated time per sample → the fixed sampler program, run on the learner's output word with ⌈P⌉ fair coins, no witness and no oracle, halts within ⌈P · S_learn(n, s, P, P)⌉ on every coin string; reason: literal machine reading of Problem 1.1
--   - encoding: fair random bits, with no additional input in the random-bit supply → HaltsWithin includes CoinsInBounds: every readCoin address is below the supplied tape length; reason: the RAM sentinel must not reveal the externally chosen resource bound; this also makes sampler behavior depend only on its output-word input and fair bits
--   - encoding: Definitions 4.1 and 4.2 output conjunctions and a hypothesis on every run → IsDensifier always outputs a decodable conjunction list; IsUDLearner always outputs a circuit satisfying the size bound; SolvesP11 always outputs an encoded hypothesis; reason: restores the output clauses; accuracy alone is probabilistic
--   - encoding: bounds on targets with at most n variables → IsUDLearner quantifies over every ambient n and every d ≤ n, with bounds evaluated at n; reason: states the source directly without an extra monotonicity hypothesis; inner polynomial accuracy/confidence arguments can be used as the actual subroutine inputs
-- source:
--   Zelin Li, Learning DNF from Satisfying Assignments with Membership Queries, STOC 2027 submission (manuscript sha256 2e246dc4…2670), Theorem 4.3, p. 11 (PDF 12)

import Mathlib
import Definitions.Def_DNFSatMQ_Main_Machine
open TargetedSamplers

namespace DNFSatMQ.Main

/-- Theorem 4.3 (p. 11). The bound functions take `(n, s, 1/ε, 1/δ)` ; `poly(n, s, 1/ε)` is `c (n + s + 1/ε)^c` for one `c` fixed before the input. -/
theorem theorem_4_3 (Pden Plearn : Program) (γ Tden Tlearn Slearn : ℕ → ℕ → ℝ → ℝ → ℝ)
    (hden : IsDensifier Pden γ Tden)
    (hm : ∃ c : ℕ, ∀ (n s : ℕ), 1 ≤ n → 1 ≤ s → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∀ φ : SamplingAC0.DNF (Fin n), φ.length ≤ s → (satSet φ).Nonempty →
      ∀ L : ℕ, ⌈Tden n s (1 / ε) (1 / δ)⌉₊ ≤ L →
      ∀ (r : Fin L → Bool) (w : Fin L → {x // x ∈ satSet φ}) (y : List Bool)
        (cs : List (Conj n)),
        outWord Pden (learnerTapes s (satSet φ) φ.eval ε (some δ) r w) = some y →
        decodeConjList n y = some cs →
        (cs.length : ℝ) ≤ c * ((n : ℝ) + s + 1 / ε + Real.log (1 / δ)) ^ c)
    (hγ : ∃ c : ℕ, ∀ (n s : ℕ), 1 ≤ n → 1 ≤ s → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      1 / γ n s (1 / ε) (1 / δ) ≤ c * ((n : ℝ) + s + 1 / ε + Real.log (1 / δ)) ^ c)
    (hlearn : IsUDLearner Plearn Tlearn Slearn) :
    ∃ (PL PS : Program) (c : ℕ),
      ∀ (n s : ℕ), 1 ≤ n → 1 ≤ s → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
        ∀ φ : SamplingAC0.DNF (Fin n), φ.length ≤ s → ∀ hF : (satSet φ).Nonempty,
          SolvesP11 circuitHyp PL PS
            ⌈c * ((n : ℝ) + s + 1 / ε + Tden n s (4 / ε) 4 +
                Tlearn n s (c * ((n : ℝ) + s + 1 / ε) ^ c) (c * ((n : ℝ) + s + 1 / ε) ^ c) +
                Slearn n s (c * ((n : ℝ) + s + 1 / ε) ^ c) (c * ((n : ℝ) + s + 1 / ε) ^ c)) ^ c⌉₊
            ⌈c * ((n : ℝ) + s + 1 / ε) ^ c⌉₊
            ⌈c * ((n : ℝ) + s + 1 / ε) ^ c *
                Slearn n s (c * ((n : ℝ) + s + 1 / ε) ^ c) (c * ((n : ℝ) + s + 1 / ε) ^ c)⌉₊
            ⌈c * ((n : ℝ) + s + 1 / ε + Tden n s (4 / ε) 4 +
                Tlearn n s (c * ((n : ℝ) + s + 1 / ε) ^ c) (c * ((n : ℝ) + s + 1 / ε) ^ c) +
                Slearn n s (c * ((n : ℝ) + s + 1 / ε) ^ c) (c * ((n : ℝ) + s + 1 / ε) ^ c)) ^ c⌉₊
            n s ε φ hF := by sorry

end DNFSatMQ.Main
