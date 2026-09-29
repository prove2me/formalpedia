-- Prove2me | Theorems.Thm_ElectroweakWiki_charged_boson_combination
-- name    : ElectroweakWiki.charged_boson_combination
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T20:05:20.84182+00:00
-- url     : https://prove2.me/theorems/a44bf646-8cd3-439d-9aba-8ec096ec7dd9
-- title:
--   $W^\pm = (W_1 \mp iW_2)/\sqrt2$
-- statement:
--   For real field values $W_1, W_2$ put $W^\pm = (W_1 \mp iW_2)/\sqrt 2$. Then
--
--   1. $W^- = \overline{W^+}$;
--   2. $W_1 = (W^+ + W^-)/\sqrt2$;
--   3. $W_2 = i\,(W^+ - W^-)/\sqrt2$;
--   4. $W^+W^- = \tfrac12(W_1^2+W_2^2)$.
--
--   So the charged fields carry the same information as $W_1, W_2$, and $W^+W^-$ is the real quadratic form that appears in the mass term $m_W^2 W^+_\mu W^{-\mu}$.
-- source:
--   Wikipedia, "Electroweak interaction", revision oldid=1360331872, https://en.wikipedia.org/w/index.php?title=Electroweak_interaction&oldid=1360331872; Section Formulation, 'The W1 and W2 bosons, in turn, combine to produce the charged massive bosons W±: W± = (W1 ∓ iW2)/√2' (p. 3 of the PDF)

import Definitions.Def_ElectroweakWiki_defs
open Matrix

namespace ElectroweakWiki

theorem charged_boson_combination (W1 W2 : ℝ) :
    wMinus W1 W2 = (starRingEnd ℂ) (wPlus W1 W2) ∧
      (W1 : ℂ) = (wPlus W1 W2 + wMinus W1 W2) / (Real.sqrt 2 : ℂ) ∧
      (W2 : ℂ) = Complex.I * (wPlus W1 W2 - wMinus W1 W2) / (Real.sqrt 2 : ℂ) ∧
      wPlus W1 W2 * wMinus W1 W2 = (((W1 ^ 2 + W2 ^ 2) / 2 : ℝ) : ℂ) := by sorry

end ElectroweakWiki
