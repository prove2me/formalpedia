-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_layer_sum_b
-- name    : Formalism.HermitianLatticeCounting.P.layer_sum_b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:28.279809+00:00
-- url     : https://prove2.me/theorems/4c6c0fca-baa5-46b6-8213-1254d31e9c48
-- title:
--   P: layer sum b
-- statement:
--   The P construction uses the layer sum b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/NearFarVolumeBounds.lean#L127-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/NearFarVolumeBounds.lean#L127-L193

import Definitions.Def_Formalism_FlagUnipotentLattices_CoveringRadius2
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_NuclearNormBoundHolds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.S7
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Classical

theorem Formalism.HermitianLatticeCounting.P.layer_sum_b (ι Γ : Type) [Fintype ι] (S : Finset Γ) (d : Γ → ι → ℝ) (A B K : ℝ)
    (F : ℝ → ℝ) (u w : ℕ → ℝ) (hA : 0 ≤ A) (hu : ∀ i, 0 ≤ u i) (hw : ∀ i, 0 ≤ w i)
    (hF : ∀ t, 0 ≤ F t) (hlev : ∀ t, 0 ≤ t → ∃ i, t ≤ u i ∧ F t ≤ w i)
    (hd : ∀ γ ∈ S, ∀ v, 0 ≤ d γ v)
    (hcount : ∀ r : ι → ℝ, (∀ v, 0 ≤ r v) →
      ((S.filter fun γ => ∀ v, d γ v ≤ r v).card : ℝ) ≤ A * Real.exp (B * ∑ v, r v))
    (hK : ∀ M, ∑ i ∈ range M, w i * Real.exp (B * u i) ≤ K) :
    ∑ γ ∈ S, ∏ v, F (d γ v) ≤ A * K ^ Fintype.card ι := by sorry
