-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_hcl_neg_one
-- name    : Formalism.FrobeniusOrbits.hcl_neg_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:24:09.574202+00:00
-- url     : https://prove2.me/theorems/163f8a84-1cca-4dbf-97f2-1d31d59d518e
-- title:
--   Frobenius Orbits: hcl neg one
-- statement:
--   The Frobenius Orbits construction uses the hcl neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/RealSubfieldLeCompositum.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/RealSubfieldLeCompositum.lean#L44-L45

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Theorems.Thm_Formalism_FrobeniusOrbits_ConjReal_hcl_neg_one

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
variable {e : ℕ}

theorem Formalism.FrobeniusOrbits.hcl_neg_one : hcl e (-1 : (ZMod (2 ^ (e + 2)))ˣ) = 1 := by sorry
