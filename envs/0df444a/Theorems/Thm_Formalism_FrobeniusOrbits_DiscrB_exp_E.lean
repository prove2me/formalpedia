-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_exp_E
-- name    : Formalism.FrobeniusOrbits.DiscrB.exp_E
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:40:07.832644+00:00
-- url     : https://prove2.me/theorems/aa129533-abcc-4467-84c9-8fb9df19c5fa
-- title:
--   Discr B: exp E
-- statement:
--   The Discr B construction uses the exp E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscrB.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscrB.lean#L32-L33

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

theorem Formalism.FrobeniusOrbits.DiscrB.exp_E (e : ℕ) : (2 ^ e * (e + 1) - 1) * 4 = 2 ^ (e + 2) * (e + 1) - 4 := by sorry
