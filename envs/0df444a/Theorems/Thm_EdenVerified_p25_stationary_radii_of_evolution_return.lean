-- Prove2me | Theorems.Thm_EdenVerified_p25_stationary_radii_of_evolution_return
-- name    : EdenVerified.p25_stationary_radii_of_evolution_return
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:34:27.033805+00:00
-- url     : https://prove2.me/theorems/c5c33a13-33ce-560c-b5c5-c38a2f1c2bb7
-- title:
--   Eden Verified: p25 stationary radii of evolution return
-- statement:
--   The Eden Verified construction uses the p25 stationary radii of evolution return property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1065-L1070
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1065-L1070

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p25_stationary_radii_of_evolution_return :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (h : evolution c t p = p),
    (radiusSq₁ p = 0 ∨ radiusSq₁ p = 1 ∨ radiusSq₁ p = 2) ∧
    (radiusSq₂ p = 0 ∨ radiusSq₂ p = 1 ∨ radiusSq₂ p = 2) := by sorry
