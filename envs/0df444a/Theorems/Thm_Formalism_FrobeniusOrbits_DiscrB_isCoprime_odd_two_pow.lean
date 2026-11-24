-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_isCoprime_odd_two_pow
-- name    : Formalism.FrobeniusOrbits.DiscrB.isCoprime_odd_two_pow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:41:18.929243+00:00
-- url     : https://prove2.me/theorems/e5e71a55-f302-4514-b328-f1bd4022e7ea
-- title:
--   Discr B: is Coprime odd two pow
-- statement:
--   The Discr B construction uses the is Coprime odd two pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscrB.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscrB.lean#L17-L19

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

theorem Formalism.FrobeniusOrbits.DiscrB.isCoprime_odd_two_pow {m : ℤ} (hm : Odd m) (k : ℕ) : IsCoprime m (2 ^ k) := by sorry
