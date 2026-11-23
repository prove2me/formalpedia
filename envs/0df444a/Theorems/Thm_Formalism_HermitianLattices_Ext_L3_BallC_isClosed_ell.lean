-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallC_isClosed_ell
-- name    : Formalism.HermitianLattices.Ext.L3.BallC.isClosed_ell
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:11:33.176563+00:00
-- url     : https://prove2.me/theorems/985d122c-7c1a-49c2-bb6b-b5469338bbf1
-- title:
--   Ball C: is Closed ell
-- statement:
--   The Ball C construction uses the is Closed ell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/VolumeNormSqLeOne.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/VolumeNormSqLeOne.lean#L37-L40

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

theorem Formalism.HermitianLattices.Ext.L3.BallC.isClosed_ell : IsClosed (ell a) := by sorry
