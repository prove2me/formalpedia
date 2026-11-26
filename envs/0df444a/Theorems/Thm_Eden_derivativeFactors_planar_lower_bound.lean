-- Prove2me | Theorems.Thm_Eden_derivativeFactors_planar_lower_bound
-- name    : Eden.derivativeFactors_planar_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:27:11.762101+00:00
-- url     : https://prove2.me/theorems/7cf47720-302b-47d0-b049-238b6ed14c95
-- title:
--   Eden: derivative Factors planar lower bound
-- statement:
--   The Eden construction uses the derivative Factors planar lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeConsequences.lean#L17-L26
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeConsequences.lean#L17-L26

import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_VolumeConsequences
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.derivativeFactors_planar_lower_bound (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor) (i : Fin 4) :
    Real.exp (-4 * t) ≤ derivativeFactors c t p i.castSucc := by sorry
