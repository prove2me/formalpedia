-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_sum
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.Sym.sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:02.217843+00:00
-- url     : https://prove2.me/theorems/accd2fda-f140-49ae-8c45-d3bed455785c
-- title:
--   Sym: sum
-- statement:
--   The Sym construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L88-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L88-L94

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {A : Set E} {w : E → ℝ} {m m₁ m₂ : ℤ} {N : ℕ} {K K₁ K₂ : ℝ}

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.Sym.sum {ι : Type*} (s : Finset ι) {f : ι → E → F} {Kl : ι → ℝ}
    (h : ∀ l ∈ s, Sym A w m N (Kl l) (f l)) : Sym A w m N (∑ l ∈ s, Kl l) (fun x => ∑ l ∈ s, f l x) := by sorry
