-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_card_iso_one
-- name    : Formalism.FourierDecayAlt.P.A5x7.card_iso_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:21.34956+00:00
-- url     : https://prove2.me/theorems/eb979848-156f-4747-88ec-f820d94f0548
-- title:
--   A5x7: card iso one
-- statement:
--   The A5x7 construction uses the card iso one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AddedBlockKernelSupport.lean#L429-L437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AddedBlockKernelSupport.lean#L429-L437

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x7
variable {K : Type} [CommRing K] (R : Subring K)

theorem Formalism.FourierDecayAlt.P.A5x7.card_iso_one {n n' : ℕ} {Z : Matrix (Fin n) (Fin n) K} {Z' : Matrix (Fin n') (Fin n') K}
    (hZ : IsInt R Z⁻¹) (h1 : Z * Z⁻¹ = 1) (hZ' : IsInt R Z'⁻¹) (h1' : Z' * Z'⁻¹ = 1) :
    Nat.card (isoZZ R Z Z') = 1 := by sorry
