-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Discr_real_on_adjoin
-- name    : Formalism.FrobeniusOrbits.Discr.real_on_adjoin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:45.699927+00:00
-- url     : https://prove2.me/theorems/2faa2c33-7653-4f2c-944e-23b90ae3ecf8
-- title:
--   Discr: real on adjoin
-- statement:
--   The Discr construction uses the real on adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L38-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L38-L47

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

theorem Formalism.FrobeniusOrbits.Discr.real_on_adjoin {K : Type*} [Field K] [Algebra ℚ K] (t : K) (φ : K →+* ℂ)
    (ht : starRingEnd ℂ (φ t) = φ t) : ∀ x ∈ ℚ⟮t⟯, starRingEnd ℂ (φ x) = φ x := by sorry
