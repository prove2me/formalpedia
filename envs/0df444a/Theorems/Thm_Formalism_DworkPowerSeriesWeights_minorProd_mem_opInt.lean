-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_minorProd_mem_opInt
-- name    : Formalism.DworkPowerSeriesWeights.minorProd_mem_opInt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:03:37.621076+00:00
-- url     : https://prove2.me/theorems/210db7d8-2a6c-4f00-8ad0-e67b213cbb2f
-- title:
--   Dwork Power Series Weights: minor Prod mem op Int
-- statement:
--   The Dwork Power Series Weights construction uses the minor Prod mem op Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAOp.lean#L94-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAOp.lean#L94-L105

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementI
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
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
open Formalism.IncomingBounds MvPolynomial

theorem Formalism.DworkPowerSeriesWeights.minorProd_mem_opInt {K : Type u} [NormedField K] [IsUltrametricDist K] {σ : Type}
    {N0 N1 Cn : ℕ} (row : Fin N0 → Fin N1 → MvPolynomial σ K)
    (hrow : ∀ i b, row i b ∈ opInt K σ) (p : Fin Cn → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) : minorProd row p hp I ∈ opInt K σ := by sorry
