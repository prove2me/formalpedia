-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_card_filter_resChar_le
-- name    : Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.card_filter_resChar_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:32:58.908908+00:00
-- url     : https://prove2.me/theorems/4cd1bcc8-aca3-45f3-ba11-70e6855200bf
-- title:
--   Ideal Norm Inequalities: card filter res Char le
-- statement:
--   The Ideal Norm Inequalities construction uses the card filter res Char le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFilterResCharLe.lean#L72-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFilterResCharLe.lean#L72-L99

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
set_option linter.deprecated false

theorem Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.card_filter_resChar_le (s : Finset {P : Ideal (𝓞 K) // P.IsMaximal}) (n : ℕ) :
    (s.filter (fun P => resChar P.1 = n)).card ≤ finrank ℚ K := by sorry
