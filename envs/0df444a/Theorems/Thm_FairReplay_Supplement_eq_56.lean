-- Prove2me | Theorems.Thm_FairReplay_Supplement_eq_56
-- name    : FairReplay.Supplement.eq_56
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:57:06.393207+00:00
-- url     : https://prove2.me/theorems/de35f6a3-6bad-4f25-ac21-fa7d40049abd
-- title:
--   Theorem 10.6, eq. (56) — every $\delta$-correct suite tester has $\mathbb E_0[T]\ge\mathrm{kl}(1-\delta,\delta)/(r\log\frac{r}{r-d})$
-- statement:
--   Let $H$ have at least one fairness edge, $p,s,d>0$ with $p+s+d<1$, $\delta\in(0,1/2)$ and $r=1-p-s$. Every adaptive tester whose primitive observation is a synchronized suite-replay round, which is $\delta$-correct for the null against the alternative changing an active vertex $x$, and whose stopping time has finite null expectation, satisfies
--   $$\mathbb E_0[T]\ \ge\ \frac{\mathrm{kl}(1-\delta,\delta)}{r\log\frac{r}{r-d}}.$$
--
--   So suite replay cannot beat the single-edge four-way rate of Theorem 10.4.
--
--   Differences from the source:
--   - generalization: δ-correct against the union of all single-changed-endpoint alternatives → δ-correct against one fixed alternative x ∈ V+(H); reason: the paper's hypothesis implies the Lean one for every x, so the Lean theorem specializes to the paper's
--   - encoding: an adaptive (δ-correct) tester → a triple (π, T, ψ) on the published sequential-sampling model: possibly randomized adaptive policy, stopping time of the transcript filtration (⊤ = never stops), decision measurable for the stopped σ-algebra; type II counts non-stopping as an error; reason: the tester model of the published base mission; randomized policies contain the deterministic ones, so the class is at least the paper's
--   - encoding: the round reveals its ordered raw Boolean outputs → the output vector is passed to the model through the injective real code obsCode; laws are images of the uniform tape on [0, 1]; reason: an injective code loses no information, so the tester sees the whole transcript
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.6, eq. (56), p.17 (PDF p.19)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_FairReplay_IsDeltaCorrect
import Definitions.Def_FairReplay_expectedRounds
import Definitions.Def_FairReplay_Supplement_activeVertices
import Definitions.Def_FairReplay_Supplement_suiteModel

open MeasureTheory

namespace FairReplay.Supplement

/-- **Theorem 10.6, eq. (56), the suite lower bound** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0…), Theorem 10.6, p.17 (PDF p.19)):
"Moreover, every adaptive δ-correct tester whose primitive observation is a synchronized suite-replay
round and whose stopping time has finite expectation satisfies, on the null,
E0[T] ≥ kl(1 − δ, δ) / (r log(r/(r−d))), r = 1 − p − s. (56)"

For a graph `H` with at least one edge, `p, s, d > 0` with `p + s + d < 1`, `δ ∈ (0, 1/2)` and any active
vertex `x`: every suite tester that is δ-correct for the null against the alternative changing `x` and has
`E₀[T] < ∞` satisfies `E₀[T] ≥ kl(1 − δ, δ)/(r log(r/(r − d)))`, `r = 1 − p − s`.

**Formalization Note** The tester is assumed δ-correct against one fixed alternative only, which is
implied by δ-correctness against the union of all alternatives. Testers are adaptive stopping rules
on suite rounds with a decision measurable for the stopped σ-algebra. -/
theorem eq_56 {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hE : 1 ≤ H.edgeFinset.card) (p s d δ : ℝ) (hp : 0 < p) (hs : 0 < s) (hd : 0 < d)
    (hpsd : p + s + d < 1) (hδ : 0 < δ) (hδ2 : δ < 1 / 2) (x : Fin n)
    (hx : x ∈ activeVertices H) (π : BanditAlgorithm.BanditPolicy 1)
    (T : (ℕ → Fin 1 × ℝ) → ℕ∞) (ψ : (ℕ → Fin 1 × ℝ) → Bool)
    (hT : BanditAlgorithm.IsBanditStoppingTime T) (hψ : Measurable[hT.measurableSpace] ψ)
    (hcorr : IsDeltaCorrect δ (suiteModel H p s d none) (suiteModel H p s d (some x)) π T ψ)
    (hfin : expectedRounds (suiteModel H p s d none) π T < ⊤) :
    ENNReal.ofReal (BanditAlgorithm.bernoulliRelativeEntropy (1 - δ) δ /
        ((1 - p - s) * Real.log ((1 - p - s) / ((1 - p - s) - d)))) ≤
      expectedRounds (suiteModel H p s d none) π T := by sorry

end FairReplay.Supplement
