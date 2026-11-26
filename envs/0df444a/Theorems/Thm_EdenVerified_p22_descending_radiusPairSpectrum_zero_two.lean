-- Prove2me | Theorems.Thm_EdenVerified_p22_descending_radiusPairSpectrum_zero_two
-- name    : EdenVerified.p22_descending_radiusPairSpectrum_zero_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:50:09.057876+00:00
-- url     : https://prove2.me/theorems/faad0991-77ae-5c1d-a7dc-c9210d818216
-- title:
--   Eden Verified: p22 descending radius Pair Spectrum zero two
-- statement:
--   The Eden Verified construction uses the p22 descending radius Pair Spectrum zero two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1740-L1743
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1740-L1743

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p22_descending_radiusPairSpectrum_zero_two :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 0 2) = ![0, -2, -2, -4, -c] := by sorry
