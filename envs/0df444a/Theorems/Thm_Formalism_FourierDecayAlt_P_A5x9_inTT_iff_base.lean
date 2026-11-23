-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_inTT_iff_base
-- name    : Formalism.FourierDecayAlt.P.A5x9.inTT_iff_base
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:46:07.096719+00:00
-- url     : https://prove2.me/theorems/9cc9a5dd-1105-49f7-9910-0ba969c148c1
-- title:
--   A5x9: in TT iff base
-- statement:
--   The A5x9 construction uses the in TT iff base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L788-L812
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L788-L812

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

theorem Formalism.FourierDecayAlt.P.A5x9.inTT_iff_base (Z₀ Z₀' p p' : Matrix (Fin n) (Fin n) K) (hp : IsPP R k p)
    (hp' : IsPP R k p') (φ : coker R (Z₀ * p) ≃ₗ[R] coker R (Z₀' * p')) :
    InTT R (k + 1) (Z₀ * p) (Z₀' * p') φ ↔ ∃ D, IsD R k D ∧ ∀ v v' : Fin n → R,
      φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' →
        ∀ j, (abelian₂ R k Z₀' v' - D *ᵥ abelian₂ R k Z₀ v) j ∈ R := by sorry
