-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallC_convex_ell
-- name    : Formalism.HermitianLattices.Ext.L3.BallC.convex_ell
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:45:03.607931+00:00
-- url     : https://prove2.me/theorems/70363f83-0b57-45ef-a3e7-a6b98c92d321
-- title:
--   Ball C: convex ell
-- statement:
--   The Ball C construction uses the convex ell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/VolumeNormSqLeOne.lean#L70-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/VolumeNormSqLeOne.lean#L70-L94

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

theorem Formalism.HermitianLattices.Ext.L3.BallC.convex_ell (ha : ∀ i, 0 < a i) : Convex ℝ (ell a) := by sorry
