-- Prove2me | Theorems.Thm_FengLiYangMatching_General_lemma_4_1
-- name    : FengLiYangMatching.General.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:48:07.877207+00:00
-- url     : https://prove2.me/theorems/82580b11-5fbd-44b7-b70c-759858ac96ae
-- title:
--   Lemma 4.1 — conditional independent arrival times
-- statement:
--   Let G be a finite simple graph whose edge times are independent uniform [0,1]. Throughout, 0≤a<b≤3/8 and 0≤p≤2/3, as imposed on p. 6. H_b records T_b and only the times of edges in T_b. Let τ_v be its accepted matching time, or +∞ if v is unmatched. Conditional on H_b, the times outside T_b are mutually independent, with
--
--   $$t_{uv}\sim U(\min\{\tau_u,\tau_v,b\},1).$$
--
--   The formal statement identifies the explicit product law by its probability, measurability and disintegration properties on every measurable time event and history event. This supplies a genuine conditional experiment for the recovery analysis.
--
--   Differences from the source:
--   - encoding: arbitrary finite vertex set and unordered simple edges → Fin n for every n including zero, Sym2 edges and finite sets; reason: finite relabelling covers every source instance; loops are excluded in graphs and valid local configurations
--   - encoding: conditional on the exact accepted-edge history H_b → almost every history under its pushforward law, integrated against the explicit residual product law; reason: exact histories can have zero probability; Lemma 4.1 asserts measurability and disintegration, identifying this law as the conditional distribution
--   - encoding: continuous arrival times with shadow matching at phase boundaries → strict prefixes, half-open reserve/retain phases and fixed sorting of tied times; reason: the phases agree with Algorithm 1; arrivals at any fixed boundary and ties have probability zero; the same convention is used throughout
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, STOC 2027 submission #1018 (October 2026), Lemma 4.1, p. 13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf

import Definitions.Def_FengLiYangMatching_General_Local

open MeasureTheory Finset
open scoped BigOperators

namespace FengLiYangMatching.General

theorem lemma_4_1 {n : ℕ} (G : SimpleGraph (Fin n)) (a b p : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 3/8)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2/3) :
    Measurable (history G b) ∧
    (∀ A : Set (Times G), MeasurableSet A →
      Measurable (fun h : History n => residualLaw G b h A)) ∧
    (∀ᵐ h ∂historyLaw G b, IsProbabilityMeasure (residualLaw G b h)) ∧
    (∀ S : Set (History n), MeasurableSet S → ∀ A : Set (Times G), MeasurableSet A →
      arrivalLaw G (A ∩ (history G b) ⁻¹' S) =
        ∫⁻ h in S, residualLaw G b h A ∂historyLaw G b) := by sorry

end FengLiYangMatching.General
