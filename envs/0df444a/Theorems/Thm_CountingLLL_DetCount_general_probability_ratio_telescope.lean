-- Prove2me | Theorems.Thm_CountingLLL_DetCount_general_probability_ratio_telescope
-- name    : CountingLLL.DetCount.general_probability_ratio_telescope
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:15:31.172899+00:00
-- url     : https://prove2.me/theorems/9e7c3dc6-4b24-4641-a6f3-c2b731ed220a
-- title:
--   Telescoping a satisfaction-probability ratio from any base family
-- statement:
--   For any CSP satisfying Condition 1.1, any constraint families B subset H, and any injective enumeration of H\B, the ratio of satisfaction probabilities P(B)/P(H) equals the product of the reciprocal marginal factors for successively adding those constraints to B. This general telescope is the factor used in Lemma 5.1 with B equal to the distant free constraints and H equal to the root-deleted family.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, proof of Lemma 5.1, Section 5.1, PDF p.16, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Expansion
open CountingLLL.DetCount

theorem CountingLLL.DetCount.general_probability_ratio_telescope (Φ : CSP) (hΦ : Φ.Condition11)
    (B H : Finset (Fin Φ.m)) (hBH : B ⊆ H)
    (e : Fin (H \ B).card → Fin Φ.m)
    (he : Function.Injective e ∧ ∀ j, e j ∈ H \ B) :
    Φ.prob (Φ.SatAll B) / Φ.prob (Φ.SatAll H) =
      ∏ j : Fin (H \ B).card, 1 / (1 - Φ.r (Φ.prefixFam B e j) (e j)) := by sorry
