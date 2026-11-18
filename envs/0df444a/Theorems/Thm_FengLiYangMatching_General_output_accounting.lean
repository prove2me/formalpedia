-- Prove2me | Theorems.Thm_FengLiYangMatching_General_output_accounting
-- name    : FengLiYangMatching.General.output_accounting
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T18:20:06.698031+00:00
-- url     : https://prove2.me/theorems/2551eb1b-a12a-4a4c-8a6e-2a4205ef6d0d
-- title:
--   Algorithm 1 — expected retained-shadow and recovery decomposition
-- statement:
--   Run Algorithm 1 on a finite simple graph $G$ with $0\le a<b=3/8$ and reservation probability $p=5/11$. Let $T_a,T_b$ be its shadow matchings, and let $Z_{XY},Z_{YY}$ count recovery edges of the two allowed endpoint types. These counts are integrable and
--
--   $$
--   \mathbb E[\operatorname{ALG}(G)]=\mathbb E[|T_b|]-\frac5{11}\mathbb E[|T_a|]+\mathbb E[Z_{XY}+Z_{YY}].
--   $$
--
--   This separates retained shadow edges from recovery edges in the actual algorithm's output. The subtracted term accounts for independently reserved early shadow edges.
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, Improved Bounds for Online Matching with Random Edge Arrivals, STOC 2027 submission #1018, Algorithm 1, p. 3; Sections 2.2–2.3, pp. 8–9, expected matching size before time b; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf

import Definitions.Def_FengLiYangMatching_General_Local
open MeasureTheory Finset
open scoped BigOperators

namespace FengLiYangMatching.General

theorem output_accounting {n : ℕ} (G : SimpleGraph (Fin n))
    (a : ℝ) (ha : 0 ≤ a) (hab : a < 3/8) :
    Integrable (fun t => ((shadowAt G t a).card : ℝ)) (arrivalLaw G) ∧
    Integrable (fun t => ((shadowAt G t (3/8)).card : ℝ)) (arrivalLaw G) ∧
    Integrable (fun w => ZXY G a (3/8) w + ZYY G a (3/8) w) (sampleLaw G (5/11)) ∧
    (∫ w, ALG G a (3/8) w ∂sampleLaw G (5/11)) =
      (∫ t, ((shadowAt G t (3/8)).card : ℝ) ∂arrivalLaw G) -
      (5/11 : ℝ)*(∫ t, ((shadowAt G t a).card : ℝ) ∂arrivalLaw G) +
      (∫ w, ZXY G a (3/8) w + ZYY G a (3/8) w ∂sampleLaw G (5/11)) := by sorry

end FengLiYangMatching.General
