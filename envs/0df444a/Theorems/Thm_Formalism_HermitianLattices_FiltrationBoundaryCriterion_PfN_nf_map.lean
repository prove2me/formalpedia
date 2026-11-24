-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_nf_map
-- name    : Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.nf_map
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:48:56.446955+00:00
-- url     : https://prove2.me/theorems/33e40970-ba05-4947-864e-719df96fa038
-- title:
--   Pf N: nf map
-- statement:
--   The Pf N construction uses the nf map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/DifferentIdealConditions.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/DifferentIdealConditions.lean#L13-L23

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.FiltrationBoundaryCriterion
open Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
open Ideal UniqueFactorizationMonoid

theorem Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.nf_map {S : Type*} [CommRing S] [IsDedekindDomain S] (I : Ideal S) (hI : I ≠ ⊥)
    (f : Ideal S ≃* Ideal S) : normalizedFactors (f I) = (normalizedFactors I).map f := by sorry
