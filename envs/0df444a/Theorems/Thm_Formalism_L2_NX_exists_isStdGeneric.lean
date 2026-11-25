-- Prove2me | Theorems.Thm_Formalism_L2_NX_exists_isStdGeneric
-- name    : Formalism.L2.NX.exists_isStdGeneric
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:46:12.213398+00:00
-- url     : https://prove2.me/theorems/3f477086-fa59-47dd-9ac1-faa496a5798b
-- title:
--   NX: exists is Std Generic
-- statement:
--   The NX construction uses the exists is Std Generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L246-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L246-L255

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
variable {ι : Type} [Fintype ι] {p : ι → ℕ} {r : ℕ}

theorem Formalism.L2.NX.exists_isStdGeneric {K : Type} [Field K] (hp : ∀ x, (p x).Prime)
    (hζ : ∀ x, ∃ ζ : K, IsPrimitiveRoot ζ (p x)) : ∃ ψ : Uup p r →* Kˣ, IsStdGeneric p r ψ := by sorry
