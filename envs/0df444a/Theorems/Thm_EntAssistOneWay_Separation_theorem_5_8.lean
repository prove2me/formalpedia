-- Prove2me | Theorems.Thm_EntAssistOneWay_Separation_theorem_5_8
-- name    : EntAssistOneWay.Separation.theorem_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:34.028742+00:00
-- url     : https://prove2.me/theorems/5e800e95-9dd6-4943-ab02-f965d408800a
-- title:
--   Theorem 5.8 — trace moments of shifted matrix averages
-- statement:
--   Let $G,\zeta,D$ satisfy the standing assumptions, let $S=\mathbb F_2^r$ with $r\ge1$, and let $d\ge1$. Suppose each $O_s:G^S\to\operatorname{Herm}(d)$ obeys $\|O_s(h)\|_\infty\le1$ and $\mathbb E_{\phi\in\mathbb F_3}O_s(\zeta^\phi h)=0$ for every $s,h$. Put $T(g_1,g_2)=\mathbb E_sO_s(g_1\operatorname{shift}_s(g_2))$. For every even $p\ge2$,
--   $$\mathbb E_{g_1,g_2}\operatorname{tr}(T(g_1,g_2)^p)\le d(4p/2^r)^{p/2}+d^p(2^r-1)/D.$$
--   The paper writes $O(\cdot)$; the proof's bounds (15), (16) give constant one for both displayed terms. This is the quantitative matrix-moment milestone.
--
--   Differences from the source:
--   - generalization: D is the least dimension of an irrep nontrivial on ζ → any integer D ≥ 1 for which all lower-dimensional representations kill ζ; reason: complete reducibility and unitarisability for finite groups give the source instance; the estimates use only this lower-dimensional vanishing
--   - generalization: O(d(4p/2^r)^(p/2) + d^p(2^r−1)/D) → the displayed expression with both constants equal to one; reason: Corollary 2.3 bounds (15) with one and the summand count on p. 35 bounds (16) with one
--   - encoding: Herm(d)-valued maps and real traces → complex matrices with Hermiticity hypotheses, and the real part of the trace; reason: this is the same finite-dimensional Hermitian space and each power trace is real
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), pp. 33–34, Theorem 5.8; pp. 34–35, equations (15)–(20) and their bounds

import Definitions.Def_EntAssistOneWay_Separation_GroupAnalysis

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- Theorem 5.8, pp. 33–35, with constant 1 from (15), (16). -/
theorem theorem_5_8 (G : Type) [Group G] [Fintype G] (r : ℕ) (hr : 1 ≤ r)
    (ζ : G) (D : ℕ) (hζ : CentralThree ζ) (hD : DimensionGap ζ D)
    (d : ℕ) (hd : 1 ≤ d)
    (O : ShiftSpace r → (ShiftSpace r → G) → Matrix (Fin d) (Fin d) ℂ)
    (hHerm : ∀ s h, (O s h).IsHermitian)
    (hBound : ∀ s h, spectralNorm (O s h) ≤ 1)
    (hMean : ∀ s h, uniformAverage (fun φ : ZMod 3 => O s (phaseArray ζ φ h)) = 0)
    (p : ℕ) (hp : Even p) (hp₂ : 2 ≤ p) :
    uniformAverage (fun t : ShiftAlice G r => (momentOperator O t.1 t.2 ^ p).trace.re) ≤
      (d : ℝ) * (4 * (p : ℝ) / (2 : ℝ) ^ r) ^ (p / 2) +
        (d : ℝ) ^ p * ((2 : ℝ) ^ r - 1) / D := by sorry

end

end EntAssistOneWay.Separation
