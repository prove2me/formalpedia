-- Prove2me | Theorems.Thm_DistributedMWC440_UpperBound_lemma_7_7
-- name    : DistributedMWC440.UpperBound.lemma_7_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:26:13.015216+00:00
-- url     : https://prove2.me/theorems/a87ee1f6-c395-45cf-9902-541826436d11
-- title:
--   Lemma 7.7 (Approximation ratio and success probability for long-hop cycles)
-- statement:
--   Fix a minimum cycle with the stated long-hop threshold and a fixed positive exponent in $\alpha\ge n^a$. Sample skeletons first. On good samples the near-optimum scale is selected with both displayed inequalities; the overall probability still includes bad skeleton samples. Shifts are continuous and parity bits are fresh and independent.
--
--   For $k\ge1/2$ assume
--
--   $$
--   h\in\Omega((n\log^2 n)/\alpha),\qquad
--   n^a\le\alpha\le n\quad(a>0),\qquad \epsilon\in O(1/\log n).
--   $$
--
--   On good samples use a positive scale $d(S)$ satisfying both inequalities
--
--   $$
--   2d(S)(1-O(1/\log n))\le\mathrm{OPT}
--   \le2(d(S)-2\epsilon\delta_{\max}(S)).
--   $$
--
--   One execution of LDD and extended detection, with independently refreshed shifts and parity bits conditional on $S$, produces a candidate of computed weight estimate at most
--
--   $$
--   (k+1)(1+O(1/\log n))\mathrm{OPT}
--   $$
--
--   with overall probability $\Omega(\alpha^{-1/k})$. This integrates over the entire skeleton sample; there is no favorable-sample hypothesis on that global probability. All asymptotic constants precede the unknown graph, $\alpha,k,\epsilon$, scales and output selections.
--
--   Differences from the source:
--   - generalization: positive polynomially bounded integer input lengths → arbitrary positive real lengths on the same finite connected undirected graph; reason: the stated analytic arguments use weighted path lengths and positivity only; every source input specializes to this setting
--   - encoding: asymptotic O, Omega and high-probability notation → positive constants and a size threshold quantified before the network and varying algorithm parameters; reason: this spells out the uniform asymptotic statement, retaining arbitrary real parameters and fixed polynomial confidence
--   - generalization: outputs of the specified approximate SSSP algorithm → any selection of the specified distance and parent-tree outputs, with the measure evaluated on the resulting event; reason: the lower-bound argument holds for every permitted tree choice, including the source algorithm; intended computable selections give ordinary measurable probability events
--   - reading: a scale condition involving deltaMax of the sampled center set → a positive scale chosen after the skeleton sample, admissible on every good sample, with all samples charged in the joint experiment; reason: the proof fixes a good skeleton set first and then uses the Section 6.1 scale; deltaMax depends on that set
--   - encoding: independent skeleton sampling, shifts and fresh parity bits → a finite Bernoulli mixture of conditional continuous-shift and independent parity measures; reason: samples with fewer than two centers yield no candidate rather than being assumed away
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf, Lemma 7.7, printed p. 39–40 / PDF p. 41–42.

import Definitions.Def_DistributedMWC440_UpperBound_Operations

open scoped ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section

namespace DistributedMWC440.UpperBound

theorem lemma_7_7 (a cHop epsilonBound scaleSlack : ℝ)
    (ha : 0 < a) (hc : 0 < cHop) (he : 0 < epsilonBound) (hd : 0 < scaleSlack) :
    ∃ (n₀ : ℕ) (cseg C c : ℝ), 0 < cseg ∧ 0 < C ∧ 0 < c ∧
    ∀ n ≥ max 3 n₀, ∀ (W : WGraph (Fin n)), W.graph.Connected →
      (∀ u v, W.graph.Adj u v → 0 < W.length u v) →
    ∀ (Cstar : Cycle W), IsMinimum Cstar → ∀ (α k ε : ℝ),
      (n : ℝ)^a ≤ α → α ≤ n → 1/2 ≤ k → 0 < ε → ε ≤ epsilonBound / Real.log n →
      cHop * (n*(Real.log n)^2 / α) ≤ Cstar.walk.length →
    ∀ d : Finset (Fin n) → ℝ, (∀ S, 2 ≤ S.card → 0 < d S) →
      (∀ S, GoodSample Cstar S α cseg →
        2*d S*(1-scaleSlack / Real.log n) ≤ Cstar.weight ∧
        Cstar.weight ≤ 2*(d S-2*ε*deltaMax S k (d S))) →
    ∀ run : ∀ S, 2 ≤ S.card → (δ : Shifts S) → LDDTree W S k (d S) ε δ,
    ∀ patch : ∀ S (hS : 2 ≤ S.card) (δ : Shifts S) (χ : Parities (Fin n)),
        PatchOutputs (run S hS δ) χ ⌈cseg*(n/α)*Real.log n⌉₊,
      ENNReal.ofReal (c*α^(-1/k)) ≤
        LongRunProbability W k ε α d ⌈cseg*(n/α)*Real.log n⌉₊ run patch
          ((k+1)*(1+C / Real.log n)*Cstar.weight) := by sorry

end DistributedMWC440.UpperBound
