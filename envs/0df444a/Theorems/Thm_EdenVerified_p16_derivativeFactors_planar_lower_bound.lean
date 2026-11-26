-- Prove2me | Theorems.Thm_EdenVerified_p16_derivativeFactors_planar_lower_bound
-- name    : EdenVerified.p16_derivativeFactors_planar_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:25.945848+00:00
-- url     : https://prove2.me/theorems/6d87b08f-3ae4-5cb2-bb66-37b599ef864c
-- title:
--   Eden Verified: p16 derivative Factors planar lower bound
-- statement:
--   The Eden Verified construction uses the p16 derivative Factors planar lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1497-L1501
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1497-L1501

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p16_derivativeFactors_planar_lower_bound :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor) (i : Fin 4),
    Real.exp (-4 * t) ≤ derivativeFactors c t p i.castSucc := by sorry
