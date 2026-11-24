-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_entry_bound_block3
-- name    : Formalism.FourierDecayAlt.P.Ux5.entry_bound_block3
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:22:35.560622+00:00
-- url     : https://prove2.me/theorems/3a03c176-89c5-472a-b782-c85e92ebfe58
-- title:
--   Ux5: entry bound block3
-- statement:
--   The Ux5 construction uses the entry bound block3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L592-L605
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L592-L605

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
variable {k j ρ : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux5.entry_bound_block3 {c : ℝ} {A11 : Matrix (Fin j) (Fin j) ℂ} {A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A13 : Matrix (Fin j) (Fin j) ℂ} {A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A22 : B.Mat k ρ}
    {A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A31 : Matrix (Fin j) (Fin j) ℂ}
    {A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {A33 : Matrix (Fin j) (Fin j) ℂ}
    (h11 : EB A11 c) (h12 : EB A12 c) (h13 : EB A13 c) (h21 : EB A21 c) (h22 : EB A22 c) (h23 : EB A23 c)
    (h31 : EB A31 c) (h32 : EB A32 c) (h33 : EB A33 c) : EB (blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33) c := by sorry
