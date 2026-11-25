-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_complete_of_basis
-- name    : Formalism.L2.FormalSeriesBounds.UpFBr.Pl.complete_of_basis
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:04.035217+00:00
-- url     : https://prove2.me/theorems/b9e1131e-bcc2-4e48-b1c3-bb7f14475943
-- title:
--   Pl: complete of basis
-- statement:
--   The Pl construction uses the complete of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CompleteOfBasis.lean#L34-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CompleteOfBasis.lean#L34-L66

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
variable {Z : Type} [CommRing Z] (π : Z) {A : Type} [CommRing A] [Algebra Z A] {N : ℕ}
  (β : Module.Basis (Fin N) Z A)
include β

theorem Formalism.L2.FormalSeriesBounds.UpFBr.Pl.complete_of_basis [IsAdicComplete (Ideal.span {π}) Z] :
    IsAdicComplete (Ideal.span {algebraMap Z A π}) A := by sorry
