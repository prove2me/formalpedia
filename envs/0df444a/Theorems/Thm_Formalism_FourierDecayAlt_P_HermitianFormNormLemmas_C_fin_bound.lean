-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_C_fin_bound
-- name    : Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C.fin_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:47.423819+00:00
-- url     : https://prove2.me/theorems/4ccbbdce-e074-4e1c-8027-8486e1da1e7f
-- title:
--   C: fin bound
-- statement:
--   The C construction uses the fin bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L381-L413
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L381-L413

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset

theorem Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C.fin_bound (hW : Formalism.HermitianLatticeCounting.S4.WeightedCS) {Cl J V : Type} [NormedAddCommGroup V] (U : Cl → J → V)
    (W : J → ℝ) (y : Cl → J → ℝ) (S1 M : ℝ) (hS1 : 0 ≤ S1)
    (hWpos : ∀ c j, U c j ≠ 0 → 0 < W j) (hy : ∀ c j, ‖U c j‖ ^ 2 ≤ y c j)
    (h1 : ∀ (c : Cl) (T : Finset J), (∀ j ∈ T, U c j ≠ 0) → ∑ j ∈ T, (W j)⁻¹ ≤ S1)
    (h2 : ∀ T : Finset (Cl × J), (∀ x ∈ T, U x.1 x.2 ≠ 0) → ∑ x ∈ T, W x.2 * y x.1 x.2 ≤ M)
    (Cs : Finset Cl) (T : Finset J) : ∑ c ∈ Cs, ‖∑ j ∈ T, U c j‖ ^ 2 ≤ S1 * M := by sorry
