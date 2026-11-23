-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_zpow_neg_lt_one
-- name    : Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.zpow_neg_lt_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:00.168678+00:00
-- url     : https://prove2.me/theorems/c559e441-e134-49cd-a3e2-5bbb40ac4203
-- title:
--   Ideal Norm Inequalities: zpow neg lt one
-- statement:
--   The Ideal Norm Inequalities construction uses the zpow neg lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EulerFacMulConjInvSplit.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EulerFacMulConjInvSplit.lean#L14-L16

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.HermitianLattices.Ext.L3.IdealNormInequalities

theorem Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.zpow_neg_lt_one {x : ℝ} (hx : 1 < x) {M : ℕ} (hM : 1 ≤ M) : x ^ (-(M : ℤ)) < 1 := by sorry
