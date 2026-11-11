-- Prove2me | Theorems.Thm_EntAssistOneWay_Separation_lemma_5_5
-- name    : EntAssistOneWay.Separation.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:28.93016+00:00
-- url     : https://prove2.me/theorems/7572b7fb-4c0e-4de3-a081-75e0a892a95a
-- title:
--   Lemma 5.5 — one central rotation
-- statement:
--   Let $G,\zeta,D$ satisfy the central order-three and dimension-gap assumptions. Let $Q,R:G^2\to\mathbb C$ obey $|Q|,|R|\le1$ pointwise. For independent uniform $g_0,g_1,h_0,h_1\in G$ and $\phi\in\mathbb F_3$,
--   $$\left|\mathbb E[Q(g_0h_0,g_1h_1)R(g_0h_1,g_1h_0)]-\mathbb E[Q(\zeta^\phi g_0h_0,\zeta^\phi g_1h_1)R(g_0h_1,g_1h_0)]\right|\le1/D.$$
--   This estimate concerns arbitrary bounded complex functions; the rotation has the same phase in both arguments of $Q$.
--
--   Differences from the source:
--   - generalization: D is the least dimension of an irrep nontrivial on ζ → any integer D ≥ 1 for which all lower-dimensional representations kill ζ; reason: complete reducibility and unitarisability for finite groups give the source instance; the estimates use only this lower-dimensional vanishing
--   - encoding: independent uniform group elements and a phase in F₃ → uniform average on product types with phase type ZMod 3; reason: product uniform averages express exactly the stated joint law
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 27, Lemma 5.5, equation (9)

import Definitions.Def_EntAssistOneWay_Separation_GroupAnalysis

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- Lemma 5.5, p. 27, equation (9), with independent uniform choices. -/
theorem lemma_5_5 (G : Type) [Group G] [Fintype G] (ζ : G) (D : ℕ)
    (hζ : CentralThree ζ) (hD : DimensionGap ζ D)
    (Q R : G × G → ℂ) (hQ : ∀ t, ‖Q t‖ ≤ 1) (hR : ∀ t, ‖R t‖ ≤ 1) :
    ‖uniformAverage (fun g : (G × G) × (G × G) =>
        Q (g.1.1 * g.2.1, g.1.2 * g.2.2) * R (g.1.1 * g.2.2, g.1.2 * g.2.1)) -
      uniformAverage (fun t : ((G × G) × (G × G)) × ZMod 3 =>
        Q (ζ ^ t.2.val * t.1.1.1 * t.1.2.1, ζ ^ t.2.val * t.1.1.2 * t.1.2.2) *
          R (t.1.1.1 * t.1.2.2, t.1.1.2 * t.1.2.1))‖ ≤ 1 / (D : ℝ) := by sorry

end

end EntAssistOneWay.Separation
