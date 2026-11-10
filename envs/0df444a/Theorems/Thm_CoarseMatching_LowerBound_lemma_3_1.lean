-- Prove2me | Theorems.Thm_CoarseMatching_LowerBound_lemma_3_1
-- name    : CoarseMatching.LowerBound.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:35:20.996826+00:00
-- url     : https://prove2.me/theorems/5a1e0dc3-6036-4701-92c3-19bbf5bc2f4f
-- title:
--   Lemma 3.1 — XOR-to-one-instance communication and advantage
-- statement:
--   There is an absolute $K\ge1$. Let $f:X\times Y\to\{0,1\}$ be measurable on arbitrary measurable domains, and let $\mu$ be an arbitrary probability law on $X\times Y$. For $t\ge2$, $L\ge t$, and $0<g\le1$, a local randomized protocol for the XOR of $t$ independent $\mu$-inputs, with cost at most $L$ and success at least $1/2+g/2$, implies a single-instance protocol satisfying
--
--   $$\mathrm{cost}\le KL\log(2L)g^{-K/t},\qquad\mathrm{success}\ge\frac12+\frac{g^{K/t}}{2K}.$$
--
--   Neither protocol has a round restriction. The absolute constant precedes the input domains and law. This is the paper’s communication hardness-amplification interface.
--
--   Differences from the source:
--   - encoding: randomized local two-party protocols → published binary-tree and tape primitives extended by public-coin-dependent tree choice, actual transmitted-bit costs, and Bob as final local output party; reason: public coins may choose the schedule without changing resource counts; arbitrary tape laws are retained, and swapping the arbitrary input domains handles Alice output without communication
--   - encoding: a distribution on arbitrary input domains and meaningful success probabilities → ProbabilityMeasure input laws, joint measurable execution, and measurable f; reason: the ordinary measurability convention permits arbitrary laws without an atomic or finite-domain restriction
--   - encoding: logarithm with unspecified base → natural logarithm; reason: changing logarithm base is absorbed by the existential absolute K, including its other monotone bounds
-- source:
--   Gillat Kol, Even Coarse Matching Estimates Require Nearly Linear Streaming Space, STOC 2027 submission #1135 (October 2026), Lemma 3.1, printed p. 10 (PDF p. 11). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1135.pdf

import Definitions.Def_CoarseMatching_LowerBound_ProtocolResources

open MeasureTheory

namespace CoarseMatching.LowerBound

/-- Gillat Kol, STOC 2027 submission #1135 (October 2026), Lemma 3.1,
printed p.10 / PDF p.11. Arbitrary domains and probability measures, unbounded
number of rounds. Natural logarithm; absolute constant K is unrelated to goal K.
Bob produces the answer; exchanging X and Y gives the Alice-output version. -/
theorem lemma_3_1 : ∃ K : ℝ, 1 ≤ K ∧
    ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y]
      (f : X → Y → Bool) (μ : ProbabilityMeasure (X × Y)),
      Measurable (fun xy : X × Y => f xy.1 xy.2) →
      ∀ (t : ℕ) (L g : ℝ), 2 ≤ t → (t : ℝ) ≤ L → 0 < g → g ≤ 1 →
      ∀ π : Protocol (Fin t → X) (Fin t → Y), MeasurableProtocol π →
        CostOn (fun _ _ => True) π L → 1/2 + g/2 ≤ xorSuccess t π μ f →
        ∃ σ : Protocol X Y, MeasurableProtocol σ ∧
          CostOn (fun _ _ => True) σ (K*L*Real.log (2*L)*g^(-K/(t : ℝ))) ∧
          1/2 + g^(K/(t : ℝ))/(2*K) ≤ success σ μ f := by sorry

end CoarseMatching.LowerBound
