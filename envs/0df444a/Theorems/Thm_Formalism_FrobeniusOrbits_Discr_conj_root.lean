-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Discr_conj_root
-- name    : Formalism.FrobeniusOrbits.Discr.conj_root
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:34.592394+00:00
-- url     : https://prove2.me/theorems/41be9183-dde9-4054-9403-87eb731a44fb
-- title:
--   Discr: conj root
-- statement:
--   The Discr construction uses the conj root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L12-L17

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

theorem Formalism.FrobeniusOrbits.Discr.conj_root {z : ℂ} {m : ℕ} (hm : m ≠ 0) (hz : z ^ m = 1) : starRingEnd ℂ z = z⁻¹ := by sorry
