-- Prove2me | Theorems.Thm_Formalism_ThetaLiftIndependence_GaussOperatorLemmas_sum_units_char
-- name    : Formalism.ThetaLiftIndependence.GaussOperatorLemmas.sum_units_char
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:29:15.211936+00:00
-- url     : https://prove2.me/theorems/706ade80-0c1f-4d30-870c-f81825479e03
-- title:
--   Gauss Operator Lemmas: sum units char
-- statement:
--   The Gauss Operator Lemmas construction uses the sum units char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/GaussOp.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/GaussOp.lean#L17-L25

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_GaussOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Formalism Formalism.ThetaLiftIndependence
open Formalism.ThetaLiftIndependence.GaussOperatorLemmas
variable {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]

theorem Formalism.ThetaLiftIndependence.GaussOperatorLemmas.sum_units_char (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (a : 𝔽) :
    ∑ d : 𝔽ˣ, ψ (a * d) = (if a = 0 then (Fintype.card 𝔽 : ℂ) else 0) - 1 := by sorry
