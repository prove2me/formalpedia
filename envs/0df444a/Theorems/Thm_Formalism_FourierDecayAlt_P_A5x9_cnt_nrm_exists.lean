-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_cnt_nrm_exists
-- name    : Formalism.FourierDecayAlt.P.A5x9.cnt_nrm_exists
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:50.549656+00:00
-- url     : https://prove2.me/theorems/a63927d2-8c59-460c-a8ff-c22de18fb8dd
-- title:
--   A5x9: cnt nrm exists
-- statement:
--   The A5x9 construction uses the cnt nrm exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L848-L854
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L848-L854

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
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)

theorem Formalism.FourierDecayAlt.P.A5x9.cnt_nrm_exists (Z₀ : Matrix (Fin n) (Fin n) K)
    (D : {D : Matrix (Fin n) (Fin n) K // IsD R k D}) :
    ∃ D' : {D : Matrix (Fin n) (Fin n) K // IsD R k D}, Nrm R k Z₀ D' ∧
      ∀ (x : Fin n → R) (j : Fin n), ((D'.1 - D.1) *ᵥ abelian₂ R k Z₀ x) j ∈ R := by sorry
