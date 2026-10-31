-- Prove2me | Theorems.Thm_AdviceBonus_lemma_5
-- name    : AdviceBonus.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:44:58.704185+00:00
-- url     : https://prove2.me/theorems/eedcd69e-8ff3-45ff-82ad-719efbb4faba
-- title:
--   Lemma 5 — $\bar q_1=\bar q^A_2+\int_{\bar q^A_2}^{\bar q^B_2}G(q)\,dq$ when both second cutoffs are interior (27)
-- statement:
--   Let the posterior distribution satisfy the standing assumptions, let $w>0$, and fix any compensation profile $(f_A,b_A,f_B,b_B)$. If both second-customer cutoffs are interior, $(\bar q^A_2,\bar q^B_2)\in(0,1)^2$, then the first-customer cutoff (4) is
--   $$
--   \bar q_1=\bar q^A_2+\int_{\bar q^A_2}^{\bar q^B_2}G(q)\,dq. \qquad(27)
--   $$
--
--   The integral is oriented: when $\bar q^B_2<\bar q^A_2$ it is $-\int_{\bar q^B_2}^{\bar q^A_2}G$. This expresses the first cutoff through the second ones and is the starting point of every derivative computation in the appendix.
--
--   Differences from the source:
--   - reading: q̄1 by (4), no corner convention → clamped to [0, 1]; reason: the convention of footnote 19 for (2) and (3); under the hypotheses the right-hand side of (27) lies in (0, 1), so the clamp is inactive
--   - reading: density g > 0 on [0, 1], hazard rate increasing on [0, 1] → g continuous and positive on [0, 1], hazard rate weakly increasing on [0, 1); reason: the proofs use continuity (intermediate value theorem, p.35) and the hazard rate is undefined at q = 1
--   - encoding: Z^A, Z^B include w_l → w_l dropped; reason: it cancels from Z^A − Z^B
-- source:
--   Honda–Inderst–Ottaviani, When Liability is Not Enough, SSRN 4125013 (May 2022), Appendix A, Lemma 5, eq. (27), p.31

import Mathlib
import Definitions.Def_AdviceBonus_Model

namespace AdviceBonus

/-- **Lemma 5**, eq. (27), p.31 (Honda–Inderst–Ottaviani, SSRN 4125013, May 2022). If both
second-customer cutoffs are interior, `(q̄^A_2, q̄^B_2) ∈ (0, 1)²`, then the first-customer cutoff
(4) is `q̄_1 = q̄^A_2 + ∫_{q̄^A_2}^{q̄^B_2} G(q) dq` (oriented integral). -/
theorem lemma_5 (D : Dist) (w : ℝ) (hw : 0 < w) (sA sB : ℝ × ℝ)
    (hA : q2A w sA sB ∈ Set.Ioo (0 : ℝ) 1) (hB : q2B w sA sB ∈ Set.Ioo (0 : ℝ) 1) :
    q1 D w sA sB = q2A w sA sB + ∫ q in q2A w sA sB..q2B w sA sB, D.G q := by sorry

end AdviceBonus
