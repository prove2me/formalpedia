-- Prove2me | Theorems.Thm_Formalism_ThetaLiftIndependence_FiniteFieldPlancherel_charSum
-- name    : Formalism.ThetaLiftIndependence.FiniteFieldPlancherel.charSum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:24.404131+00:00
-- url     : https://prove2.me/theorems/3f4e01bb-c514-4ad0-974f-ff0762df87fb
-- title:
--   Finite Field Plancherel: char Sum
-- statement:
--   The Finite Field Plancherel construction uses the char Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/FFPlancherel.lean#L9-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/FFPlancherel.lean#L9-L39

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

theorem Formalism.ThetaLiftIndependence.FiniteFieldPlancherel.charSum {𝔽 U : Type} [Field 𝔽] [AddCommGroup U] [Module 𝔽 U] [Fintype U]
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (g : Module.Dual 𝔽 U) :
    ∑ e : U, ψ (g e) = if g = 0 then (Fintype.card U : ℂ) else 0 := by sorry
