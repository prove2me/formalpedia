-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_mem_colSpan
-- name    : Formalism.FourierDecayAlt.P.A5x9.mem_colSpan
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:11:14.717476+00:00
-- url     : https://prove2.me/theorems/95fe6874-815c-4c2b-a32c-ef39a596f472
-- title:
--   A5x9: mem col Span
-- statement:
--   The A5x9 construction uses the mem col Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L294-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L294-L296

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
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)

theorem Formalism.FourierDecayAlt.P.A5x9.mem_colSpan (Z : Matrix (Fin n) (Fin n) K) (x : Fin n → R) :
    x ∈ colSpan R k Z ↔ ∃ t : Fin n → R, (∀ j : Fin n, k < j.val → t j = 0) ∧
      Z *ᵥ coeLin R t = coeLin R x := by sorry
