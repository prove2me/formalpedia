-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_inTT_iff
-- name    : Formalism.FourierDecayAlt.P.A5x9.inTT_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:46:04.959349+00:00
-- url     : https://prove2.me/theorems/e080f3ad-1df9-42a6-9bcb-8ae2c830993f
-- title:
--   A5x9: in TT iff
-- statement:
--   The A5x9 construction uses the in TT iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L717-L786
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L717-L786

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

theorem Formalism.FourierDecayAlt.P.A5x9.inTT_iff (Z Z' : Matrix (Fin n) (Fin n) K) (φ : coker R Z ≃ₗ[R] coker R Z') :
    InTT R (k + 1) Z Z' φ ↔ ∃ D, IsD R k D ∧ ∀ v v' : Fin n → R,
      φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' →
        ∀ j, (abelian₂ R k Z' v' - D *ᵥ abelian₂ R k Z v) j ∈ R := by sorry
