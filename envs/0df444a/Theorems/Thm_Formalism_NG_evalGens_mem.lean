-- Prove2me | Theorems.Thm_Formalism_NG_evalGens_mem
-- name    : Formalism.NG.evalGens_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:15:25.0368+00:00
-- url     : https://prove2.me/theorems/e65eb25a-dd05-4689-a437-960c2e94549a
-- title:
--   NG: eval Gens mem
-- statement:
--   The NG construction uses the eval Gens mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LenCokerOfDetNeZero.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LenCokerOfDetNeZero.lean#L21-L28

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

theorem Formalism.NG.evalGens_mem (Θ : Matrix g g R) (n : g → NN) (hrel : ∀ i, ∑ j, Θ i j • n j = 0)
    (φ : NN →ₗ[R] M) : (fun j => φ (n j)) ∈ LinearMap.ker (relMap O M Θ) := by sorry
