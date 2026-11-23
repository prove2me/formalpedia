-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_LL_ph_apply
-- name    : CompanionTheory.ThKR.LL.ph_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:22.082898+00:00
-- url     : https://prove2.me/theorems/b4ccdf8e-bcc9-4446-a6f0-86bca65f5274
-- title:
--   LL: ph apply
-- statement:
--   The LL construction uses the ph apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/IsoOfIntegral.lean#L48-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/IsoOfIntegral.lean#L48-L59

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_HasDerivAtSchwartzToL2
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l]

theorem CompanionTheory.ThKR.LL.ph_apply (S : Eu l →L[ℝ] Eu l) (f : Sch l) (x : Eu l) :
    ph S f x = exp (((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I) * f x := by sorry
