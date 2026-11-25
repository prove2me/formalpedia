-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_lift_idem
-- name    : Formalism.L2.FormalSeriesBounds.UpFBr.Pl.lift_idem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:32:40.047855+00:00
-- url     : https://prove2.me/theorems/2a8a8f56-7b43-478e-b4ec-93c160034200
-- title:
--   Pl: lift idem
-- statement:
--   The Pl construction uses the lift idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CompleteOfBasis.lean#L74-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CompleteOfBasis.lean#L74-L75

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPl
import Definitions.Def_Lemmata_MiscLemmasH_Imports
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CompleteOfBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Polynomial
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl
variable {A : Type} [CommRing A] (I : Ideal A)

theorem Formalism.L2.FormalSeriesBounds.UpFBr.Pl.lift_idem [IsAdicComplete I A] (ε : A) (h : ε * ε - ε ∈ I) : ∃ e : A, e * e = e ∧ e - ε ∈ I := by sorry
