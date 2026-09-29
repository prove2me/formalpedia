-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_exists_unit_affine_normalization
-- name    : BanditAlgorithm.partial_monitoring_exists_unit_affine_normalization
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T17:49:03.724985+00:00
-- url     : https://prove2.me/theorems/ec3990de-3985-4aa2-829f-d84eea7290df
-- title:
--   Unit-interval affine normalization of a partial-monitoring game
-- statement:
--   Every finite partial-monitoring game G=(L,Phi) admits a positive affine normalization G prime=(L prime,Phi) whose losses lie in [0,1]. More precisely, there are lambda>0 and an outcome-dependent shift c_i such that
--
--   $$
--   L prime_{a,i}=\lambda L_{a,i}+c_i
--   $$
--
--   for all actions and outcomes, with unchanged feedback. Moreover, local observability of G implies local observability of G prime.
--
--   The construction uses a finite bound on all absolute loss entries, scales by a positive common factor, and adds the same shift to every action in each outcome. Such transformations preserve every cell, neighbourhood, and local loss-difference estimator up to scaling. This is the normalization bridge from the arbitrary-real-loss classification theorem to the [0,1]-loss Algorithm 26 analysis.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Chapter 37: regret definition on p. 483 and the [0,1] loss normalization preceding Theorems 37.16--37.17 on p. 496, https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame

open scoped BigOperators

namespace BanditAlgorithm

/-! The affine normalization used between Lattimore--Szepesvári,
Theorems 37.11 and 37.15--37.17. -/

theorem partial_monitoring_exists_unit_affine_normalization
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊) :
    ∃ G' : PartialMonitoringGame k d 𝕊, ∃ lam : ℝ, ∃ c : Fin d → ℝ,
      0 < lam ∧
      (∀ a i, G'.L a i ∈ Set.Icc (0 : ℝ) 1) ∧
      (LocallyObservable G → LocallyObservable G') ∧
      (∀ a i, G'.L a i = lam * G.L a i + c i) ∧
      G'.Φ = G.Φ := by
  sorry

end BanditAlgorithm
