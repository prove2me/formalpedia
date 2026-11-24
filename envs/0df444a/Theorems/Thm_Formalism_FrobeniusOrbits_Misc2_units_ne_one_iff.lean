-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Misc2_units_ne_one_iff
-- name    : Formalism.FrobeniusOrbits.Misc2.units_ne_one_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:11:51.702921+00:00
-- url     : https://prove2.me/theorems/62d44b8a-643d-4e73-afb0-c1cb4388449a
-- title:
--   Misc2: units ne one iff
-- statement:
--   The Misc2 construction uses the units ne one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CardExtendedGaloisGroup.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CardExtendedGaloisGroup.lean#L32-L33

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Misc2

theorem Formalism.FrobeniusOrbits.Misc2.units_ne_one_iff (x : ℤˣ) : x ≠ 1 ↔ x = -1 := by sorry
