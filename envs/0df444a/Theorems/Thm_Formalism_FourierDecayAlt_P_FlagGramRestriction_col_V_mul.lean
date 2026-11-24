-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FlagGramRestriction_col_V_mul
-- name    : Formalism.FourierDecayAlt.P.FlagGramRestriction.col_V_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:44:45.442132+00:00
-- url     : https://prove2.me/theorems/71aed6f5-a034-498b-bc67-e88a6ae8c31a
-- title:
--   Flag Gram Restriction: col V mul
-- statement:
--   The Flag Gram Restriction construction uses the col V mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagGramRestriction.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagGramRestriction.lean#L20-L23

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FlagGramRestriction
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector UnipotentUpperFacts
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.FlagGramRestriction.col_V_mul (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (Φ : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) (j : Fin (r + 1) ⊕ Fin (r + 1)) :
    (fun a => (gnB k r z z' γ * Φ) a j) = ∑ i, Φ i j • gramVec k r z z' γ i := by sorry
