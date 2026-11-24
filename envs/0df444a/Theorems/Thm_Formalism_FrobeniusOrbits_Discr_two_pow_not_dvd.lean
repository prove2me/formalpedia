-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Discr_two_pow_not_dvd
-- name    : Formalism.FrobeniusOrbits.Discr.two_pow_not_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:23.699865+00:00
-- url     : https://prove2.me/theorems/c2d13f93-dadb-4794-8e39-ad12607e7962
-- title:
--   Discr: two pow not dvd
-- statement:
--   The Discr construction uses the two pow not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L49-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L49-L56

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

theorem Formalism.FrobeniusOrbits.Discr.two_pow_not_dvd (e : ℕ) : ¬ (2 ^ (e + 2)) ∣ 2 := by sorry
