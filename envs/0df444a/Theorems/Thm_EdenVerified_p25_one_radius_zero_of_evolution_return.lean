-- Prove2me | Theorems.Thm_EdenVerified_p25_one_radius_zero_of_evolution_return
-- name    : EdenVerified.p25_one_radius_zero_of_evolution_return
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:36:25.255216+00:00
-- url     : https://prove2.me/theorems/8ab58455-553c-40e6-b17d-86025b2cc230
-- title:
--   Eden Verified: p25 one radius zero of evolution return
-- statement:
--   The Eden Verified construction uses the p25 one radius zero of evolution return property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1083-L1087
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1083-L1087

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p25_one_radius_zero_of_evolution_return :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (h : evolution c t p = p),
    radiusSq₁ p = 0 ∨ radiusSq₂ p = 0 := by sorry
