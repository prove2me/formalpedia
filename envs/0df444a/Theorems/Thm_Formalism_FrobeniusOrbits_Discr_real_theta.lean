-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Discr_real_theta
-- name    : Formalism.FrobeniusOrbits.Discr.real_theta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:34.542133+00:00
-- url     : https://prove2.me/theorems/31ddb9c3-9f2f-4c4f-8218-2b3abaac01db
-- title:
--   Discr: real theta
-- statement:
--   The Discr construction uses the real theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L19-L23

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

theorem Formalism.FrobeniusOrbits.Discr.real_theta {K : Type*} [Field K] {m : ℕ} (hm : m ≠ 0) {ζ : K} (hζ : IsPrimitiveRoot ζ m)
    (ψ : K →+* ℂ) : starRingEnd ℂ (ψ (ζ + ζ⁻¹)) = ψ (ζ + ζ⁻¹) := by sorry
