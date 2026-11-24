-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_derivation_prod
-- name    : Formalism.L2.FormalSeriesBounds.S4.derivation_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:46.029863+00:00
-- url     : https://prove2.me/theorems/39d3f6f8-a6f0-459a-abab-cecaa57d945e
-- title:
--   S4: derivation prod
-- statement:
--   The S4 construction uses the derivation prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L315-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L315-L322

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.S4
variable {R : Type*} [CommRing R]

theorem Formalism.L2.FormalSeriesBounds.S4.derivation_prod {F : Type*} [CommRing F] [Algebra R F] {n : ℕ} (D : Derivation R F F)
    (χ : Fin n → F) (b : Fin n → R) (hD : ∀ σ, D (χ σ) = b σ • χ σ) (s : Finset (Fin n)) :
    D (∏ σ ∈ s, χ σ) = (∑ σ ∈ s, b σ) • ∏ σ ∈ s, χ σ := by sorry
