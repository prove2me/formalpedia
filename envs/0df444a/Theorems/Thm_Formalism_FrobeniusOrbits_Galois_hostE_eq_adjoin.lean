-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Galois_hostE_eq_adjoin
-- name    : Formalism.FrobeniusOrbits.Galois.hostE_eq_adjoin
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:53:05.781436+00:00
-- url     : https://prove2.me/theorems/caa3ed27-2c5f-42e4-8dda-d56741fdffee
-- title:
--   Galois: host E eq adjoin
-- statement:
--   The Galois construction uses the host E eq adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L213-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L213-L218

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Galois
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem Formalism.FrobeniusOrbits.Galois.hostE_eq_adjoin (ζ a b : L) : hostE ζ a b = ℚ⟮ζ + ζ⁻¹, a, b⟯ := by sorry
