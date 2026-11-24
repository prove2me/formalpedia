-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_firstFamilyOperatorEnd_limUnder_of_step
-- name    : Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd.limUnder_of_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:30.766267+00:00
-- url     : https://prove2.me/theorems/1d0bc9b0-05db-4ae4-bd9e-b25653a6b6f1
-- title:
--   first Family Operator End: lim Under of step
-- statement:
--   The first Family Operator End construction uses the lim Under of step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FirstFamilyOperatorEnd.lean#L12-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FirstFamilyOperatorEnd.lean#L12-L33

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEleventh
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FirstFamilyOperatorEnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd
open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans traceDeterminantCongruences reductionMapsOfForms localValuationFiltration hermitianFormColumns vectorCountBounds

theorem Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd.limUnder_of_step {u : ℕ → ℕ} {q e k₀ : ℕ} (hq : 0 < q)
    (h : ∀ k, k₀ ≤ k → u (k + 1) = q ^ e * u k) {k : ℕ} (hk : k₀ ≤ k) :
    limUnder atTop (fun k : ℕ => (u k : ℝ) / (q : ℝ) ^ (k * e)) = (u k : ℝ) / (q : ℝ) ^ (k * e) := by sorry
