-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallC_isBounded_ell
-- name    : Formalism.HermitianLattices.Ext.L3.BallC.isBounded_ell
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:41.707846+00:00
-- url     : https://prove2.me/theorems/c7b353df-f155-4e01-bf4f-8333cae21ae7
-- title:
--   Ball C: is Bounded ell
-- statement:
--   The Ball C construction uses the is Bounded ell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/VolumeNormSqLeOne.lean#L96-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/VolumeNormSqLeOne.lean#L96-L112

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VolumeNormSqLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallC
variable {M : ℕ} (a : Fin M → ℝ)
variable {a}

theorem Formalism.HermitianLattices.Ext.L3.BallC.isBounded_ell (ha : ∀ i, 0 < a i) : Bornology.IsBounded (ell a) := by sorry
