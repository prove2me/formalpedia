-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x2_sum_addChar_norm_sq
-- name    : Formalism.FourierDecayAlt.P.A6x2.sum_addChar_norm_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:12.23282+00:00
-- url     : https://prove2.me/theorems/941ebc36-bb63-4d3c-b897-9d60ede40f55
-- title:
--   A6x2: sum add Char norm sq
-- statement:
--   The A6x2 construction uses the sum add Char norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PosSemidefEntryBound.lean#L13-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PosSemidefEntryBound.lean#L13-L44

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PosSemidefEntryBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x2

theorem Formalism.FourierDecayAlt.P.A6x2.sum_addChar_norm_sq (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (G : Type)
    [AddCommGroup G] [Fintype G] (v : G → E) :
    ∑ χ : AddChar G ℂ, ‖∑ g, χ (-g) • v g‖ ^ 2 = (Fintype.card G : ℝ) * ∑ g, ‖v g‖ ^ 2 := by sorry
