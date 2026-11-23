-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Discr_th_coe
-- name    : Formalism.FrobeniusOrbits.Discr.th_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:27.288106+00:00
-- url     : https://prove2.me/theorems/47275768-b9d0-4e1b-be84-70feda0133d8
-- title:
--   Discr: th coe
-- statement:
--   The Discr construction uses the th coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L72-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L72-L72

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscriminantRealSubfield
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.FrobeniusOrbits.Discr
variable {K : Type*} [Field K] [NumberField K] {e : ℕ} {z : K}

theorem Formalism.FrobeniusOrbits.Discr.th_coe (z : K) : ((th z : ℚ⟮z + z⁻¹⟯) : K) = z + z⁻¹ := by sorry
