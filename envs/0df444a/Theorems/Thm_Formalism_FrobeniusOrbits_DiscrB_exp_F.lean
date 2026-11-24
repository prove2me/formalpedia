-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_exp_F
-- name    : Formalism.FrobeniusOrbits.DiscrB.exp_F
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:40:04.892319+00:00
-- url     : https://prove2.me/theorems/9c1724ac-56b0-400f-8449-4c0c6c2c6052
-- title:
--   Discr B: exp F
-- statement:
--   The Discr B construction uses the exp F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscrB.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscrB.lean#L35-L36

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

theorem Formalism.FrobeniusOrbits.DiscrB.exp_F (e : ℕ) : (2 ^ e * (e + 1) - 1) * 2 = 2 ^ (e + 1) * (e + 1) - 2 := by sorry
