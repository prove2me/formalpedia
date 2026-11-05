-- Prove2me | Theorems.Thm_BlindNRMLS_lemma_EC_4
-- name    : BlindNRMLS.lemma_EC_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:50:23.884957+00:00
-- url     : https://prove2.me/theorems/ccac1e10-baca-4211-a68f-5f24fa84b17c
-- title:
--   Lemma EC.4 (corrected: the identity had $p$ and $q$ swapped) — Bernoulli KL bound
-- statement:
--   For $p,q\in(0,1)$,
--   $$
--   D_{\mathrm{KL}}(\mathrm{Ber}(p)\|\mathrm{Ber}(q))=p\log\frac pq+(1-p)\log\frac{1-p}{1-q}\le\frac{1}{\min\{p,q,1-p,1-q\}}|p-q|^2 .
--   $$
--   This is the only divergence estimate in the lower bound's change of measure.
--
--   Differences from the source:
--   - correction: D_KL(Ber(p)‖Ber(q)) = q log(q/p) + (1−q) log((1−q)/(1−p)) → D_KL(Ber(p)‖Ber(q)) = p log(p/q) + (1−p) log((1−p)/(1−q)); reason: the printed right side is D_KL(Ber(q)‖Ber(p)): at (¼,½) it is 0.1438 against the true 0.1308
--   - encoding: a real-valued divergence → InformationTheory.klDiv in [0,∞], equal to ofReal of the closed form; reason: Lean convention; the identity also says it is finite
-- source:
--   Simchi-Levi, Xu & Zhao, Blind Network Revenue Management and Bandits with Knapsacks Under Limited Switches, arXiv:1911.01067v5, Lemma EC.4, p.ec51

import Mathlib
import Definitions.Def_BlindNRMLS_hardProblem

open MeasureTheory
open scoped ENNReal

namespace BlindNRMLS

/-- Lemma EC.4 (corrected): for `p, q ∈ (0,1)`,
`D_KL(Ber(p) ‖ Ber(q)) = p log(p/q) + (1-p) log((1-p)/(1-q)) ≤ |p-q|²/min{p, q, 1-p, 1-q}`.
Simchi-Levi, Xu & Zhao, arXiv:1911.01067v5, Lemma EC.4, p.ec51.

**Formalization Note.** The printed identity has `p` and `q` swapped: it is `D_KL(Ber(q) ‖ Ber(p))`.
The divergence is `InformationTheory.klDiv`, valued in `ℝ≥0∞`, so the identity includes its
finiteness. -/
theorem lemma_EC_4 (p q : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1) (hq₀ : 0 < q) (hq₁ : q < 1) :
    InformationTheory.klDiv (bernoulliLaw p) (bernoulliLaw q) =
        ENNReal.ofReal (p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))) ∧
      p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) ≤
        1 / min (min p q) (min (1 - p) (1 - q)) * |p - q| ^ 2 := by sorry

end BlindNRMLS
