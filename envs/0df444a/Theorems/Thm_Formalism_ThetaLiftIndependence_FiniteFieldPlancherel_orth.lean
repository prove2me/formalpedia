-- Prove2me | Theorems.Thm_Formalism_ThetaLiftIndependence_FiniteFieldPlancherel_orth
-- name    : Formalism.ThetaLiftIndependence.FiniteFieldPlancherel.orth
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:47:44.374301+00:00
-- url     : https://prove2.me/theorems/42f8eac9-d309-4c7b-b31d-aa86da5a53e1
-- title:
--   Finite Field Plancherel: orth
-- statement:
--   The Finite Field Plancherel construction uses the orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/FFPlancherel.lean#L41-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/FFPlancherel.lean#L41-L52

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_FFPlancherel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ThetaLiftIndependence
open Formalism.ThetaLiftIndependence.FiniteFieldPlancherel
open Classical

theorem Formalism.ThetaLiftIndependence.FiniteFieldPlancherel.orth {𝔽 U : Type} [Field 𝔽] [AddCommGroup U] [Module 𝔽 U] [Fintype U]
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) [Fintype 𝔽] (f g : Module.Dual 𝔽 U) :
    ∑ e : U, star (ψ (f e)) * ψ (g e) = if f = g then (Fintype.card U : ℂ) else 0 := by sorry
