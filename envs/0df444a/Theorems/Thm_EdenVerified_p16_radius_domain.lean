-- Prove2me | Theorems.Thm_EdenVerified_p16_radius_domain
-- name    : EdenVerified.p16_radius_domain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:52:30.225495+00:00
-- url     : https://prove2.me/theorems/cb824927-320d-55cf-8ac4-69a34fa14257
-- title:
--   Eden Verified: p16 radius domain
-- statement:
--   The Eden Verified construction uses the p16 radius domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1852-L1858
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1852-L1858

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p16_radius_domain (c : ℝ) {p : PhaseSpace} (hp : p ∈ attractor)
    {t : ℝ} (ht : 0 ≤ t) : ∀ τ ∈ Icc (0 : ℝ) t,
      radiusSq₁ (evolution c τ p) ∈ Icc (0 : ℝ) 2 ∧
      radiusSq₂ (evolution c τ p) ∈ Icc (0 : ℝ) 2 := by sorry
