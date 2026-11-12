-- Prove2me | Theorems.Thm_DictatorsCK_Main_lemma_4_4
-- name    : DictatorsCK.Main.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:41:00.494198+00:00
-- url     : https://prove2.me/theorems/4bee6138-cea6-4d70-ba1a-2a0ed0d20cec
-- title:
--   Lemma 4.4 — edge entropy comparison: edge production $\ge B_e(|d|)$
-- statement:
--   For $x_-,x_+\in(-1,1)$, put $e=\frac{H(x_+)+H(x_-)}{2}$ (average endpoint entropy, nats) and $d=\frac{x_+-x_-}{2}$ (half-difference). With $B_e(q)=qF^{-1}(e/q)$, $B_e(0)=0$, where $F(v)=H(\tanh v)/\tanh v$,
--   $$\frac{(x_+-x_-)(\operatorname{atanh}x_+-\operatorname{atanh}x_-)}{4}\ge B_e(|d|).$$
--
--   The left side is the entropy production of one cube edge; the profile $B$ is the exact production of a centered edge, and the lemma says it is a lower bound for every edge with the same average entropy and half-difference. The source cites it from Chen–Gohari–Nair [CGN25, Lemma 10].
--
--   Differences from the source:
--   - encoding: F⁻¹ : (0, ∞) → (0, ∞), the inverse of the bijection F → Finv y = a chosen v > 0 with F(v) = y (0 when there is none); reason: F is a strictly decreasing bijection of (0, ∞) (Lemma 4.1), so the chosen v is the inverse; the default is never used, since every argument of F⁻¹ here is positive
-- source:
--   Ky, Tran, Dictators are most informative, arXiv:2609.24184 (held copy, sha256 aa2515fb…0a2c7f), p. 22 (PDF 23), Lemma 4.4

import Mathlib
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_DictatorsCK_Main_Information
import Definitions.Def_DictatorsCK_Main_Profile

open OAI.LeanBlast.CourtadeKumar

namespace DictatorsCK.Main

theorem lemma_4_4 (xm xp : ℝ) (hm : -1 < xm ∧ xm < 1) (hp : -1 < xp ∧ xp < 1) :
    Bprof ((entropy xp + entropy xm) / 2) |(xp - xm) / 2| ≤
      (xp - xm) * (Real.artanh xp - Real.artanh xm) / 4 := by sorry

end DictatorsCK.Main
