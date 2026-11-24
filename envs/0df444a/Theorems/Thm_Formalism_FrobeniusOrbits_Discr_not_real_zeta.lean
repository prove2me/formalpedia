-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Discr_not_real_zeta
-- name    : Formalism.FrobeniusOrbits.Discr.not_real_zeta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:21.868797+00:00
-- url     : https://prove2.me/theorems/51d531eb-6f03-4640-8d10-b26190f91fb7
-- title:
--   Discr: not real zeta
-- statement:
--   The Discr construction uses the not real zeta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L25-L36

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

theorem Formalism.FrobeniusOrbits.Discr.not_real_zeta {K : Type*} [Field K] {m : ℕ} (hm : m ≠ 0) (h2 : ¬ m ∣ 2) {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) (ψ : K →+* ℂ) : starRingEnd ℂ (ψ ζ) ≠ ψ ζ := by sorry
