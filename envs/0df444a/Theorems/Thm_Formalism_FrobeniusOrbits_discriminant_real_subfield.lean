-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_discriminant_real_subfield
-- name    : Formalism.FrobeniusOrbits.discriminant_real_subfield
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:31.771467+00:00
-- url     : https://prove2.me/theorems/bc511ae5-c001-4556-8d6a-ece215405f6c
-- title:
--   Frobenius Orbits: discriminant real subfield
-- statement:
--   The Frobenius Orbits construction uses the discriminant real subfield property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L307-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean#L307-L315

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
open Discr

theorem Formalism.FrobeniusOrbits.discriminant_real_subfield : DiscrMaximalRealCyclotomic := by sorry
