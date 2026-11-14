-- Prove2me | Theorems.Thm_CountingLLL_DetCount_positive_probability_ratio_telescope
-- name    : CountingLLL.DetCount.positive_probability_ratio_telescope
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:26:33.311858+00:00
-- url     : https://prove2.me/theorems/014cfc11-0e37-4490-8fec-22730c969e78
-- title:
--   Satisfaction-ratio telescope from a feasible target family
-- statement:
--   Let B be a subset of H in a finite CSP, with at least one satisfying assignment for H. For any injective enumeration of H\B, the ratio of satisfaction probabilities P(B)/P(H) equals the product of reciprocal marginal factors obtained by adding those constraints in order. This needs only feasibility of H, not the LLL condition, and is therefore suitable for the measure expansion of Lemma 6.1.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, telescope in proof of Lemma 5.1 and Lemma 6.1, PDF pp.16,22, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Expansion
open CountingLLL.DetCount

theorem CountingLLL.DetCount.positive_probability_ratio_telescope (Φ : CSP)
    (B H : Finset (Fin Φ.m)) (hpos : 0 < Φ.Z H) (hBH : B ⊆ H)
    (e : Fin (H \ B).card → Fin Φ.m)
    (he : Function.Injective e ∧ ∀ j, e j ∈ H \ B) :
    Φ.prob (Φ.SatAll B) / Φ.prob (Φ.SatAll H) =
      ∏ j : Fin (H \ B).card, 1 / (1 - Φ.r (Φ.prefixFam B e j) (e j)) := by sorry
