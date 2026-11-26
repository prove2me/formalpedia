-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_generatedFirstBadSources_density_terminalProfile
-- name    : FirstPassageLinearTransport.generatedFirstBadSources_density_terminalProfile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:44:33.160859+00:00
-- url     : https://prove2.me/theorems/ef39715f-45d2-4d37-871b-f34e0eebaa0b
-- title:
--   First Passage Linear Transport: generated First Bad Sources density terminal Profile
-- statement:
--   Complete terminal profile for generated first-bad sources, conditional
--   only on the displayed landing-shell cardinality estimate.  The conclusion
--   has no dependence on the number of recursive re-certification stages.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalProfile.lean#L163-L258
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalProfile.lean#L163-L258

import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.generatedFirstBadSources_density_terminalProfile
    {M L U H : ℕ} {r : ℚ} {t b b' c' : ℝ}
    (hr : 0 < r) (hUM : U < M) (hL1 : 1 ≤ L)
    (hsmall : ∀ q ∈ Finset.Icc L U,
      ((((q + 2 : ℕ) : ℚ) / r) / ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3)
    (hlanding : ∀ q ∈ Finset.Icc L U,
      ((landingBad q t).card : ℝ) ≤
        1 + (2 : ℝ) ^ q *
          Real.exp (-(((q - 1 : ℕ) : ℝ) * b)))
    (hb' : 0 < b') (hbb' : b' < b)
    (hc' : 0 < c') (hc2 : c' < Real.log 2) :
    ((generatedFirstBadSources M L U H r t).card : ℝ) /
        (2 : ℝ) ^ M ≤
      (H : ℝ) * (1 + 6 / (r : ℝ)) *
        terminalTailBound b b' c' L := by sorry
