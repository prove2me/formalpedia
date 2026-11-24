-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_odd_of_mod
-- name    : Formalism.FrobeniusOrbits.DiscrB.odd_of_mod
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:57:48.631409+00:00
-- url     : https://prove2.me/theorems/a4139afd-3993-4ec1-a3c3-40898b87d9b9
-- title:
--   Discr B: odd of mod
-- statement:
--   The Discr B construction uses the odd of mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscrB.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscrB.lean#L38-L39

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

theorem Formalism.FrobeniusOrbits.DiscrB.odd_of_mod {q : ℕ} (h : q % 2 = 1) : Odd (q : ℤ) := by sorry
