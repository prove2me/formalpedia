-- Prove2me | Theorems.Thm_Formalism_ThetaLiftIndependence_GaussOperatorLemmas_core
-- name    : Formalism.ThetaLiftIndependence.GaussOperatorLemmas.core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:22:10.834252+00:00
-- url     : https://prove2.me/theorems/86006da5-a783-4c90-94b3-99dd7c48ea39
-- title:
--   Gauss Operator Lemmas: core
-- statement:
--   The Gauss Operator Lemmas construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/GaussOp.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/GaussOp.lean#L27-L32

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

theorem Formalism.ThetaLiftIndependence.GaussOperatorLemmas.core (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : 𝔽ˣ →* (V →ₗ[ℂ] V)) (v : V) (hv : ∑ c : 𝔽ˣ, ρ c v = 0) :
    ∑ e : 𝔽ˣ, (∑ d : 𝔽ˣ, ψ (((e : 𝔽) - 1) * d)) • ρ e v = (Fintype.card 𝔽 : ℂ) • v := by sorry
