-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_minorProd_map
-- name    : Formalism.DworkPowerSeriesWeights.minorProd_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:51.642867+00:00
-- url     : https://prove2.me/theorems/b6cf5d22-068f-4c85-b65c-ce29a8924ab0
-- title:
--   Dwork Power Series Weights: minor Prod map
-- statement:
--   The Dwork Power Series Weights construction uses the minor Prod map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneRow.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneRow.lean#L16-L25

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneRow
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
open MvPolynomial

theorem Formalism.DworkPowerSeriesWeights.minorProd_map {R : Type u} [CommRing R] {σ τ : Type} {N0 N1 Cn : ℕ}
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (row : Fin N0 → Fin N1 → MvPolynomial σ R) (p : Fin Cn → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) :
    φ (minorProd row p hp I) = minorProd (fun i b => φ (row i b)) p hp I := by sorry
