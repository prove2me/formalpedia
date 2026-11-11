-- Prove2me | Theorems.Thm_EntAssistOneWay_Separation_lemma_5_6
-- name    : EntAssistOneWay.Separation.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:41.337029+00:00
-- url     : https://prove2.me/theorems/94ffcf48-f0e2-40d6-afe7-d3f4383d2a95
-- title:
--   Lemma 5.6 — spectral bound for the phase-complement mixing operator
-- statement:
--   Let $G$ be a finite group, $\zeta\in Z(G)$ have order three, and let $D\ge1$ satisfy the representation dimension gap. On $\mathbb C^{G\times G}$ take $K,P$ as defined on p. 28. Then
--   $$\|(I-P)K\|_\infty\le1/D.$$
--   The norm is the operator norm induced by Euclidean coordinates. This bound controls the change caused by a central phase rotation.
--
--   Differences from the source:
--   - generalization: D is the least dimension of an irrep nontrivial on ζ → any integer D ≥ 1 for which all lower-dimensional representations kill ζ; reason: complete reducibility and unitarisability for finite groups give the source instance; the estimates use only this lower-dimensional vanishing
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 29, Lemma 5.6; p. 28, equation (10) and definitions of K, P

import Definitions.Def_EntAssistOneWay_Separation_GroupAnalysis

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- Lemma 5.6, p. 29; D need only satisfy the representation gap. -/
theorem lemma_5_6 (G : Type) [Group G] [Fintype G] (ζ : G) (D : ℕ)
    (hζ : CentralThree ζ) (hD : DimensionGap ζ D) :
    spectralNorm ((1 - phaseP ζ) * mixingK G) ≤ 1 / (D : ℝ) := by sorry

end

end EntAssistOneWay.Separation
