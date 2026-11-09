-- Prove2me | Theorems.Thm_CommThresholdPR_StrongConverse_fact_2_4
-- name    : CommThresholdPR.StrongConverse.fact_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:33.147906+00:00
-- url     : https://prove2.me/theorems/555ba225-293a-4bf3-9037-288bedb65cff
-- title:
--   Fact 2.4 — conditional entropy and information continuity
-- statement:
--   For finite joint laws $q_{ZW},P_{ZW}$ with $\operatorname{TV}(q_{ZW},P_{ZW})\le\delta\le1/2$,
--   $$|H_q(Z\mid W)-H_P(Z\mid W)|\le\delta\log_2|Z|+h(\delta).$$
--   For finite joint laws $q_{XYH},P_{XYH}$ within total variation $\delta\le1/2$, also
--   $$\left|I_q(X;H\mid Y)+I_q(Y;H\mid X)-I_P(X;H\mid Y)-I_P(Y;H\mid X)\right|\le2L_{\rm in}\delta+4h(\delta).$$
--   Here $h$ is binary entropy in bits and $L_{\rm in}=\log_2(|X||Y|)$. Both absolute-value inequalities are retained. The bound depends only on the input alphabet, not the alphabet of $H$.
--
--   Differences from the source:
--   - encoding: finite joint laws, base-two information and conditioning at positive-probability values → Mathlib PMF laws, finite entropy differences and explicit positive-probability conditional rows; reason: the representation changes no finite distribution; support mismatches retain infinite divergence and null conditional rows are used only as arbitrary normalized fallbacks
-- source:
--   Daiki Suruga, The Exact Communication Threshold for Parallel Repetition, STOC 2027 submission #304 (October 2026), Fact 2.4, p. 9, (11)–(12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/304.pdf

import Definitions.Def_CommThresholdPR_StrongConverse_Simulation

namespace CommThresholdPR.StrongConverse

theorem fact_2_4 :
    (∀ {Z W : Type} [Fintype Z] [Fintype W] (q P : PMF (Z × W)) (δ : ℝ),
      tv q P ≤ δ → δ ≤ 1 / 2 →
      |condEntropy q Prod.fst Prod.snd - condEntropy P Prod.fst Prod.snd| ≤
        δ * Real.logb 2 (Fintype.card Z) + WildeQIT.binaryEntropy δ) ∧
    (∀ {X Y H : Type} [Fintype X] [Fintype Y] [Fintype H]
      (q P : PMF (X × Y × H)) (δ : ℝ), tv q P ≤ δ → δ ≤ 1 / 2 →
      |(cmi q Prod.fst (fun z => z.2.2) (fun z => z.2.1) +
          cmi q (fun z => z.2.1) (fun z => z.2.2) Prod.fst) -
        (cmi P Prod.fst (fun z => z.2.2) (fun z => z.2.1) +
          cmi P (fun z => z.2.1) (fun z => z.2.2) Prod.fst)| ≤
        2 * logInput X Y * δ + 4 * WildeQIT.binaryEntropy δ) := by sorry

end CommThresholdPR.StrongConverse
