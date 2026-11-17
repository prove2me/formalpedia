-- Prove2me | Theorems.Thm_FairReplay_Supplement_theorem_10_6_eq_54_55
-- name    : FairReplay.Supplement.theorem_10_6_eq_54_55
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:56:27.848076+00:00
-- url     : https://prove2.me/theorems/3308e49d-6c90-4c37-b209-ae3e5f0fae04
-- title:
--   Theorem 10.6, eqs. (54)–(55) — suite replay detects every single changed endpoint in $\lceil\log\delta/\log(1-d)\rceil$ rounds
-- statement:
--   Let $H$ have at least one fairness edge, fix $p,s,d>0$ with $p+s+d<1$ and $\delta\in(0,1/2)$. Under the null every active vertex has old threshold $p$ and new threshold $p+s$; under the alternative for $x\in V_+(H)$, the vertex $x$ has new threshold $p+s+d$. There is one test using
--   $$T_{\mathrm{suite}}=\Big\lceil\frac{\log\delta}{\log(1-d)}\Big\rceil$$
--   synchronized suite-replay rounds that has zero type-I error and type-II error at most $\delta$ under every single-changed-endpoint alternative. Its concrete execution cost is
--   $$2n_+\Big\lceil\frac{\log\delta}{\log(1-d)}\Big\rceil,\qquad n_+=|V_+(H)|.$$
--
--   The round count has no factor depending on the number of edges.
--
--   Differences from the source:
--   - encoding: the union of all single-changed-endpoint alternatives → alternatives indexed by the changed vertex x ∈ V+(H); one tester, type II ≤ δ for each; reason: "exactly one endpoint of an active edge" is a vertex of V+(H)
--   - encoding: concrete execution cost → 2·|V+(H)|·T on every run; reason: each suite round executes both versions at the n+ active inputs
--   - encoding: a test using n rounds → a tester whose stopping time is identically n; reason: fixed sample size, the reading of the published base mission (the paper's tests run exactly n rounds)
--   - encoding: an adaptive (δ-correct) tester → a triple (π, T, ψ) on the published sequential-sampling model: possibly randomized adaptive policy, stopping time of the transcript filtration (⊤ = never stops), decision measurable for the stopped σ-algebra; type II counts non-stopping as an error; reason: the tester model of the published base mission; randomized policies contain the deterministic ones, so the class is at least the paper's
--   - encoding: the round reveals its ordered raw Boolean outputs → the output vector is passed to the model through the injective real code obsCode; laws are images of the uniform tape on [0, 1]; reason: an injective code loses no information, so the tester sees the whole transcript
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.6, eqs. (54)–(55), pp.16–17 (PDF pp.18–19)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_FairReplay_Supplement_activeVertices
import Definitions.Def_FairReplay_Supplement_suiteModel

open MeasureTheory

namespace FairReplay.Supplement

/-- **Theorem 10.6, eqs. (54)–(55), the synchronized suite test** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0…), Theorem 10.6, pp.16–17
(PDF pp.18–19)): "Let H = (V, E) contain at least one fairness edge and fix p, s, d > 0 with
p + s + d < 1 and δ ∈ (0, 1/2). [...] There is a test that distinguishes the null from the union of all
single-changed-endpoint alternatives using Tsuite = ⌈log δ / log(1 − d)⌉ (54) synchronized
suite-replay rounds, with zero type-I error and type-II error at most δ for every alternative. Hence
its concrete execution cost is 2n+ ⌈log δ / log(1 − d)⌉. (55)"

For a graph `H` with at least one edge, `p, s, d > 0` with `p + s + d < 1` and `δ ∈ (0, 1/2)`, there is one
suite tester `(π, T, ψ)` with `T ≡ T_suite = ⌈log δ / log(1 − d)⌉` that never rejects under the null and,
for every active vertex `x`, fails to reject with probability at most `δ` under the alternative changing
`x`; its concrete execution cost, `2 n+` executions per round with `n+ = |V+(H)|`, is
`2 n+ ⌈log δ / log(1 − d)⌉` on every run.

**Formalization Note** The single-changed-endpoint alternatives are indexed by the changed vertex
`x ∈ V+(H)`; the same tester must work for all of them. "A test using n rounds" means `T ≡ n`. -/
theorem theorem_10_6_eq_54_55 {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hE : 1 ≤ H.edgeFinset.card) (p s d δ : ℝ) (hp : 0 < p) (hs : 0 < s) (hd : 0 < d)
    (hpsd : p + s + d < 1) (hδ : 0 < δ) (hδ2 : δ < 1 / 2) :
    ∃ (π : BanditAlgorithm.BanditPolicy 1) (T : (ℕ → Fin 1 × ℝ) → ℕ∞)
      (ψ : (ℕ → Fin 1 × ℝ) → Bool) (hT : BanditAlgorithm.IsBanditStoppingTime T),
      Measurable[hT.measurableSpace] ψ ∧
      (∀ ω, T ω = ((⌈Real.log δ / Real.log (1 - d)⌉₊ : ℕ) : ℕ∞)) ∧
      BanditAlgorithm.banditTrajMeasure (suiteModel H p s d none) π
          {ω | T ω < ⊤ ∧ ψ ω = true} = 0 ∧
      (∀ x ∈ activeVertices H,
        BanditAlgorithm.banditTrajMeasure (suiteModel H p s d (some x)) π
          {ω | ¬ (T ω < ⊤ ∧ ψ ω = true)} ≤ ENNReal.ofReal δ) ∧
      (∀ ω, (2 * (activeVertices H).card : ℕ∞) * T ω =
        ((2 * (activeVertices H).card * ⌈Real.log δ / Real.log (1 - d)⌉₊ : ℕ) : ℕ∞)) := by sorry

end FairReplay.Supplement
