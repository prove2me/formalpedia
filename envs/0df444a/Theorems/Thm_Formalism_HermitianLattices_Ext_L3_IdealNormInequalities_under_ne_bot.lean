-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_under_ne_bot
-- name    : Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.under_ne_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:11:56.906376+00:00
-- url     : https://prove2.me/theorems/1060d072-6726-49d1-a96d-fefc45eb703b
-- title:
--   Ideal Norm Inequalities: under ne bot
-- statement:
--   The Ideal Norm Inequalities construction uses the under ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFilterResCharLe.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFilterResCharLe.lean#L15-L18

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.under_ne_bot {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : P.under ℤ ≠ ⊥ := by sorry
