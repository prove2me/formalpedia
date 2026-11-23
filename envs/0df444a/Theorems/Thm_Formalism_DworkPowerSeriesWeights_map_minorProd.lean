-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_map_minorProd
-- name    : Formalism.DworkPowerSeriesWeights.map_minorProd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:03:19.313815+00:00
-- url     : https://prove2.me/theorems/013d18fa-b50b-4bec-b882-f053ac249f78
-- title:
--   Dwork Power Series Weights: map minor Prod
-- statement:
--   The Dwork Power Series Weights construction uses the map minor Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L381-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L381-L390

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.map_minorProd {R : Type u} [CommRing R] {σ σ' : Type} {N0 N1 C : ℕ}
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ' R)
    (row : Fin N0 → Fin N1 → MvPolynomial σ R) (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) :
    φ (minorProd row p hp I) = minorProd (fun i b => φ (row i b)) p hp I := by sorry
