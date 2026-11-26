-- Prove2me | Theorems.Thm_EdenVerified_p22_descending_radiusPairSpectrum_zero_zero
-- name    : EdenVerified.p22_descending_radiusPairSpectrum_zero_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:49:56.682567+00:00
-- url     : https://prove2.me/theorems/14eaec80-fc2b-4372-be53-0da1f77f319a
-- title:
--   Eden Verified: p22 descending radius Pair Spectrum zero zero
-- statement:
--   The Eden Verified construction uses the p22 descending radius Pair Spectrum zero zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1730-L1733
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1730-L1733

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p22_descending_radiusPairSpectrum_zero_zero :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 0 0) = ![-2, -2, -2, -2, -c] := by sorry
