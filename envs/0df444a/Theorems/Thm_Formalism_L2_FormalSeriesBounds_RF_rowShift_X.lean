-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_rowShift_X
-- name    : Formalism.L2.FormalSeriesBounds.RF.rowShift_X
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:46:46.969463+00:00
-- url     : https://prove2.me/theorems/fea96d65-900f-483a-b7e8-51fdd19050df
-- title:
--   RF: row Shift X
-- statement:
--   The RF construction uses the row Shift X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowInvariant.lean#L25-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowInvariant.lean#L25-L38

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
variable {T : Type} {r : T → ℕ} {n : ℕ} {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.RF.rowShift_X (σ : T) (i i' : Fin (r σ)) (t : C) (ℓ : Letter T r n) :
    rowShift r n C σ i i' t (X ℓ) =
      if keyL ℓ = (σ, i.val, ℓ.2.2) then X ℓ + MvPolynomial.C t * X ⟨σ, i', ℓ.2.2⟩ else X ℓ := by sorry
