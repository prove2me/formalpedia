-- Prove2me | Theorems.Thm_Formalism_NG_evalGens_inj
-- name    : Formalism.NG.evalGens_inj
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:15:41.810992+00:00
-- url     : https://prove2.me/theorems/1ee76ac7-587f-42de-96c0-c6c957a164f1
-- title:
--   NG: eval Gens inj
-- statement:
--   The NG construction uses the eval Gens inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LenCokerOfDetNeZero.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LenCokerOfDetNeZero.lean#L30-L33

import Definitions.Def_Formalism_CharacterColumnKernels_StatementX
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module IsDiscreteValuationRing Matrix
noncomputable section
open Formalism Formalism.NG
variable {R O M NN : Type*} [Ring R] [CommRing O] [AddCommGroup M] [Module R M] [Module O M]
  [SMulCommClass R O M] [AddCommGroup NN] [Module R NN] {g : Type} [Fintype g]

theorem Formalism.NG.evalGens_inj (n : g → NN) (hspan : Submodule.span R (Set.range n) = ⊤) :
    Function.Injective (fun (φ : NN →ₗ[R] M) (j : g) => φ (n j)) := by sorry
