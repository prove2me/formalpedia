-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_span_resChar
-- name    : Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.span_resChar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:56.41844+00:00
-- url     : https://prove2.me/theorems/564632c8-4b6d-43ad-97f5-982083437338
-- title:
--   Ideal Norm Inequalities: span res Char
-- statement:
--   The Ideal Norm Inequalities construction uses the span res Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFilterResCharLe.lean#L13-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFilterResCharLe.lean#L13-L13

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

theorem Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.span_resChar (P : Ideal (𝓞 K)) : Ideal.span {(resChar P : ℤ)} = P.under ℤ := by sorry
