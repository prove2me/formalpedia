-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_Supplement_lemma_A_4
-- name    : BirthdayEntropy.Soundness.Supplement.lemma_A_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T21:21:54.660032+00:00
-- url     : https://prove2.me/theorems/06603869-6edf-48aa-9a75-23cfd64bad7b
-- title:
--   Lemma A.4 — Rare-coordinate bias versus answer entropy
-- statement:
--   For real numbers $0<\lambda<1$ and $0\le x\le\lambda/4$, let $d(x\|\lambda)$ be binary relative entropy with $0\log0=0$. Then both inequalities hold:
--
--   $$d(x\|\lambda)-x\log2\ge\lambda\left(\frac34-\frac{\log8}{4}\right)>\frac{2\lambda}{9}.$$
--
--   The result separates rare-coordinate bias from the surviving answer-entropy budget, with the exact intermediate constant and the strict final inequality.
--
--   Differences from the source:
--   - encoding: continuous endpoint binary divergence → published bernoulliRelativeEntropy at x=0 allowed; reason: lambda is strictly between zero and one, so the total real formula agrees with both endpoint limits
-- source:
--   Alexandru Popa, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, Lemma A.4, PDF p20 / printed p19

import Mathlib
import Definitions.Def_bernoulliRelativeEntropy

namespace BirthdayEntropy.Soundness.Supplement

/-- Lemma A.4, (26), PDF p20 / printed p19. Both the precise gap and its
strict numerical lower bound; x=0 is included. -/
theorem lemma_A_4 (lam x : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hx0 : 0 ≤ x) (hxlam : x ≤ lam / 4) :
    lam * (3/4 - Real.log 8 / 4) ≤
        BanditAlgorithm.bernoulliRelativeEntropy x lam - x * Real.log 2 ∧
      2 * lam / 9 < lam * (3/4 - Real.log 8 / 4) := by sorry

end BirthdayEntropy.Soundness.Supplement
