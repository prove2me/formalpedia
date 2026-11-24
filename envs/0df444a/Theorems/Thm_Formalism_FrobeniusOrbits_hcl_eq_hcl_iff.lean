-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_hcl_eq_hcl_iff
-- name    : Formalism.FrobeniusOrbits.hcl_eq_hcl_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:27:08.951394+00:00
-- url     : https://prove2.me/theorems/3b1cfed6-b33c-40b7-bb89-edecb88e78d3
-- title:
--   Frobenius Orbits: hcl eq hcl iff
-- statement:
--   The Frobenius Orbits construction uses the hcl eq hcl iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/RealSubfieldLeCompositum.lean#L19-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/RealSubfieldLeCompositum.lean#L19-L35

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
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

theorem Formalism.FrobeniusOrbits.hcl_eq_hcl_iff (u v : (ZMod (2 ^ (e + 2)))ˣ) :
    hcl e u = hcl e v ↔ u = v ∨ u = -v := by sorry
