-- Prove2me | Theorems.Thm_DPVerify_Supplement_theorem_5_1
-- name    : DPVerify.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:57:53.253667+00:00
-- url     : https://prove2.me/theorems/596011ab-3266-4d5b-84fd-6ef18b0648f3
-- title:
--   Theorem 5.1 — an $\varepsilon$-DP one-message proof that $D$ is a product distribution with $O(\sqrt N/(\sigma\sqrt\varepsilon)+\sqrt N/\sigma^2+1/(\sigma^2\varepsilon))$ samples
-- statement:
--   Let $\mathcal X=A_1\times\cdots\times A_d$ with finite nonempty $A_i$, $N=|\mathcal X|=\prod_i|A_i|$ and $m=\sum_i|A_i|$, and define
--   $$\Lambda(N,\sigma,\varepsilon)=\frac{\sqrt N}{\sigma\sqrt\varepsilon}+\frac{\sqrt N}{\sigma^2}.$$
--   There are universal constants $c_*>0$ and $C>0$ such that for all $d$, all $A_1,\dots,A_d$, all $\varepsilon\in(0,1]$ and $\sigma\in(0,1/12)$ with
--   $$\Lambda(N,\sigma,\varepsilon)\le c_*N, \tag{1}$$
--   there is a one-message proof protocol for "$D$ is a product distribution" — the prover sends purported marginals $M=(M^{(i)}_a)_{i\in[d],a\in A_i}$ (arbitrary reals), then the verifier, an admissible program of the randomized real RAM, reads its sample $S\sim D^s$ and decides — with:
--
--   1. **Privacy.** For every message $M$ and every pair of samples differing in one entry, the probability of acceptance and the probability of non-acceptance each change by at most a factor $e^{\varepsilon}$ ($\varepsilon$-DP of the transcript (message, decision)).
--   2. **Completeness.** If $D$ is a product distribution and the prover sends the exact marginals of $D$, the verifier accepts with probability at least $2/3$.
--   3. **Soundness.** If $\mathrm{TV}(D,Q)\ge\sigma$ for every product distribution $Q$ on $\mathcal X$, then for every message the verifier accepts with probability at most $1/3$.
--   4. **Samples.** $s\le C\Big(\dfrac{\sqrt N}{\sigma\sqrt\varepsilon}+\dfrac{\sqrt N}{\sigma^2}+\dfrac1{\sigma^2\varepsilon}\Big)$.
--   5. **Running time.** For every distribution $D$ and every message, the expected number of executed instructions is at most $C\,(m+ds+\sigma^{-4}\log N)$.
--   6. **Communication.** The message consists of $m=\sum_i|A_i|$ reals.
--
--   This is the paper's upper bound for private independence verification: with a prover, the sample complexity matches unassisted private identity testing and the verifier runs in time polynomial in $d$, $s$ and $1/\sigma$, instead of time scaling with $N$.
--
--   **Formalization Note** The protocol (sample size $s$ and program) may depend on $d$, the $A_i$, $\sigma$ and $\varepsilon$, never on $D$ or the message; $c_*$ and $C$ are chosen before everything. $\sigma$, $\varepsilon$ and the message are written in the machine's input memory. Probabilities are over $S\sim D^s$ and the machine's random streams; a run that never halts does not accept. $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: "real-RAM operations" (p.26), model unspecified → the randomized sample-access real RAM `DPVerify.Supplement.Instr` (published `SmaleNinth` core plus floor, sample access, $\mathrm{Unif}[0,1]$ and $\mathrm{Lap}(1)$ draws, unit cost per instruction, rational literals, parameters and message in the input memory); reason: the paper names the real-RAM model and charges one unit per arithmetic operation and per draw (§5.2.4).
--   - reading: "After $O(m)$ preprocessing of the prover's message, its expected verifier running time is $O(m+ds+\sigma^{-4}\log N)$" → the total expected running time, preprocessing included, is at most $C(m+ds+\sigma^{-4}\log N)$ for every message; reason: the $O(m)$ preprocessing is absorbed in the $m$ term, so the two forms are equivalent, and the paper's verifier rejects invalid messages after the $O(m)$ validation.
--   - reading: $O(\cdot)$ bounds and "universal constant $c_*$" → constants $c_*,C>0$ quantified before $d$, the $A_i$, $\sigma$, $\varepsilon$, $D$ and the message, one $C$ for the sample and time bounds; reason: the only reading with content, uniform in all parameters as the proof gives.
--   - encoding: "communication cost from the prover is $O(\sum_i|A_i|)$" → the message type is exactly $\prod_i\mathbb R^{A_i}$, i.e. $\sum_i|A_i|$ reals; reason: §5.1.1 fixes the message to the purported marginals, so the bound holds with constant $1$ by construction.
--   - encoding: finite nonempty $A_i$, distributions on $\mathcal X$ → `Fin (n i)` with $n_i\ge1$, `PMF`s; ε-DP over transcripts (message, decision) → for every fixed message, the two decision events (accept, not accept); reason: relabelling and the transcript space of a one-message protocol; deterministic messages suffice since randomized provers are mixtures.
--   - reading: adjacent datasets differ "by the addition or removal of one element" (Definition 2.1, p.4) → `PrivLearn.Generic.Neighbors`, samples of the fixed size $s$ that differ in one entry; reason: the verifier's sample size $s$ is fixed by the protocol, and the paper's own privacy arguments use substitution (§5.2.3, p.25: "neighboring input datasets map to datasets differing in at most one observation"; §6, p.33: "differ on the $i$th coordinate"), as in the base mission.
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Theorem 5.1, p.20 (PDF p.23); protocol §5.1.1, pp.20–21; proof §5.2, pp.23–26 (PDF pp.26–29)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_DPVerify_Supplement_IsProductPMF
import Definitions.Def_TTTSampling_tvDist
import Definitions.Def_DPVerify_Supplement_Instr

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace DPVerify.Supplement

/-- Theorem 5.1 (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution
Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), p.20 = PDF p.23,
protocol §5.1.1, proof §5.2, pp.20–26): with `Λ(N, σ, ε) = √N/(σ√ε) + √N/σ²`, there are
universal constants `c∗ > 0` and `C > 0` such that for every product domain
`X = A₁ × ⋯ × A_d` (`A_i = Fin (n i)`, `n i ≥ 1`, `N = ∏ᵢ n i`, `m = ∑ᵢ n i`), every
`ε ∈ (0, 1]` and `σ ∈ (0, 1/12)` with `Λ(N, σ, ε) ≤ c∗ N`, there is a sample size `s` and an
admissible verifier program `P` for the one-message protocol in which the prover first sends
purported marginals `M = (M^{(i)}_a) ∈ ∏ᵢ ℝ^{A_i}` such that:
1. (`ε`-DP) for every message `M` and adjacent samples `S, S′`, the probabilities of the decision
   bits (accept; not accept) change by at most a factor `e^ε`;
2. (completeness) if `D` is a product distribution and `M` is its exact marginals, the verifier
   accepts with probability `≥ 2/3`;
3. (soundness) if `TV(D, Q) ≥ σ` for every product distribution `Q`, then for every message the
   verifier accepts with probability `≤ 1/3`;
4. (samples) `s ≤ C (√N/(σ√ε) + √N/σ² + 1/(σ²ε))`;
5. (time) for every `D` and every message, the expected number of executed instructions is at
   most `C (m + d s + σ⁻⁴ log N)`.
The communication is the message itself, `m` reals.

**Formalization Note**
* The machine is `DPVerify.Supplement.Instr` (the published `SmaleNinth` real RAM plus floor,
  sample access, `Unif[0,1]` and `Lap(1)` draws, unit cost, rational literals); `σ`, `ε` and the
  message are in the input memory (`inputState`), the sample `S ∼ D^s` is read through
  `sampleTable S`, and probabilities are over `S` (a finite sum) and the tape.
* "After O(m) preprocessing …, expected running time O(m + ds + σ⁻⁴ log N)" is stated as one
  bound on the total expected running time, `C (m + d s + σ⁻⁴ log N)`: the `O(m)` preprocessing
  is absorbed (and a bound on the total is a bound on the part after preprocessing). The bound is
  required for every message, valid or not. `log` is the natural logarithm.
* `TV` is the published `TTTSampling.tvDist`, `½ ∑ₓ |P(x) − Q(x)|` on a finite type.
* The constants `c∗`, `C` are chosen before `d`, `n`, `σ`, `ε`; `s` and `P` may depend on
  `d, n, σ, ε` but never on `D` or the message. -/
theorem theorem_5_1 :
    ∃ cstar : ℝ, 0 < cstar ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (n : Fin d → ℕ), (∀ i, 0 < n i) →
    ∀ σ ε : ℝ, 0 < ε → ε ≤ 1 → 0 < σ → σ < 1 / 12 →
    Real.sqrt (∏ i, (n i : ℝ)) / (σ * Real.sqrt ε) + Real.sqrt (∏ i, (n i : ℝ)) / σ ^ 2
      ≤ cstar * ∏ i, (n i : ℝ) →
    ∃ (s : ℕ) (P : Program), Admissible P ∧
      -- ε-differential privacy of the transcript (message, decision bit)
      (∀ (M : (i : Fin d) → Fin (n i) → ℝ) (S S' : Fin s → (i : Fin d) → Fin (n i)),
        PrivLearn.Generic.Neighbors S S' →
          acceptProb P (sampleTable S) (inputState σ ε M)
              ≤ ENNReal.ofReal (Real.exp ε) * acceptProb P (sampleTable S') (inputState σ ε M) ∧
          rejectProb P (sampleTable S) (inputState σ ε M)
              ≤ ENNReal.ofReal (Real.exp ε) * rejectProb P (sampleTable S') (inputState σ ε M)) ∧
      -- completeness
      (∀ D : PMF ((i : Fin d) → Fin (n i)), IsProductPMF D →
        (2 / 3 : ℝ≥0∞) ≤ ∑ S : Fin s → (i : Fin d) → Fin (n i), (∏ k, D (S k)) *
          acceptProb P (sampleTable S) (inputState σ ε fun i a => (marginal D i a).toReal)) ∧
      -- soundness
      (∀ D : PMF ((i : Fin d) → Fin (n i)),
        (∀ Q : PMF ((i : Fin d) → Fin (n i)), IsProductPMF Q → σ ≤ TTTSampling.tvDist D Q) →
        ∀ M : (i : Fin d) → Fin (n i) → ℝ,
          ∑ S : Fin s → (i : Fin d) → Fin (n i), (∏ k, D (S k)) *
            acceptProb P (sampleTable S) (inputState σ ε M) ≤ (1 / 3 : ℝ≥0∞)) ∧
      -- sample complexity
      (s : ℝ) ≤ C * (Real.sqrt (∏ i, (n i : ℝ)) / (σ * Real.sqrt ε)
        + Real.sqrt (∏ i, (n i : ℝ)) / σ ^ 2 + 1 / (σ ^ 2 * ε)) ∧
      -- expected running time
      (∀ (D : PMF ((i : Fin d) → Fin (n i))) (M : (i : Fin d) → Fin (n i) → ℝ),
        ∑ S : Fin s → (i : Fin d) → Fin (n i), (∏ k, D (S k)) *
          expTime P (sampleTable S) (inputState σ ε M)
          ≤ ENNReal.ofReal (C * ((∑ i, (n i : ℝ)) + d * s
              + 1 / σ ^ 4 * Real.log (∏ i, (n i : ℝ))))) := by sorry

end DPVerify.Supplement
