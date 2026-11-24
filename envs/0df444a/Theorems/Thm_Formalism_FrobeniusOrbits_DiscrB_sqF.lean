-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_sqF
-- name    : Formalism.FrobeniusOrbits.DiscrB.sqF
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:39:57.81382+00:00
-- url     : https://prove2.me/theorems/399c2454-3c79-4a9f-a41c-ce0515224d4a
-- title:
--   Discr B: sq F
-- statement:
--   The Discr B construction uses the sq F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscrB.lean#L246-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscrB.lean#L246-L251

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscrB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField NumberField.InfinitePlace
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.DiscrB
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L]
variable {e q d : ℕ} {ζ a b : L}

theorem Formalism.FrobeniusOrbits.DiscrB.sqF (e q d : ℕ) :
    ((2 : ℤ) ^ (2 ^ (e + 1) * (e + 1) - 2) * ((q * d : ℕ) : ℤ) ^ (2 ^ e)) ^ 2 =
      (2 : ℤ) ^ (2 ^ (e + 2) * (e + 1) - 4) * ((q * d : ℕ) : ℤ) ^ (2 ^ (e + 1)) := by sorry
