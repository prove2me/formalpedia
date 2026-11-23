-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_base_last
-- name    : Formalism.FourierDecayAlt.P.A5x9.base_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:38.275983+00:00
-- url     : https://prove2.me/theorems/5f729db5-a3cd-4c32-abf4-038cfc0910ca
-- title:
--   A5x9: base last
-- statement:
--   The A5x9 construction uses the base last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1454-L1460
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1454-L1460

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
noncomputable section
variable {K : Type} [CommRing K] (R : Subring K) (k : ℕ)

theorem Formalism.FourierDecayAlt.P.A5x9.base_last (h : Point K) (s : ℕ) (t : Kˣ) (hs : 1 ≤ s) (hk : h.1.sum ≤ k) (y)
    (a b : Fin (addBlock h s t).1.sum) (ha : k < a.val) (hb : b.val + 1 = (addBlock h s t).1.sum) :
    (base R k (addBlock h s t) y)⁻¹ a b = 0 := by sorry
