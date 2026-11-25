-- Prove2me | Theorems.Thm_Formalism_L2_NX_psiStd_isStdGeneric
-- name    : Formalism.L2.NX.psiStd_isStdGeneric
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:53:57.333675+00:00
-- url     : https://prove2.me/theorems/fe122333-9024-5805-a80f-5771bbe0d178
-- title:
--   NX: psi Std is Std Generic
-- statement:
--   The NX construction uses the psi Std is Std Generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L130-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L130-L131

import Mathlib
import Definitions.Def_Formalism_AlgebraicWeights_IsAlgWeight
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.NX
variable {ι : Type} [Fintype ι] (p : ι → ℕ) (r : ℕ)
variable {r}
variable (r)
variable {p r}
variable (r)
variable {r}
variable (p r)

theorem Formalism.L2.NX.psiStd_isStdGeneric {K : Type} [Field K] (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ) (hθ : ∀ x, θ x ≠ 1) :
    IsStdGeneric p r (psiStd p r θ) := by sorry
