-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_cnta_row
-- name    : Formalism.FourierDecayAlt.P.A5x9.cnta_row
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:53.019106+00:00
-- url     : https://prove2.me/theorems/6ab75af8-f45a-4256-a0be-0e2f1ee49ca8
-- title:
--   A5x9: cnta row
-- statement:
--   The A5x9 construction uses the cnta row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L674-L715
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L674-L715

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

theorem Formalism.FourierDecayAlt.P.A5x9.cnta_row {D : Matrix (Fin n) (Fin n) K} (hD : IsD R k D) (Z : Matrix (Fin n) (Fin n) K)
    (j : Fin n) (hj : k < j.val) (v : Fin n → R) :
    (Submodule.Quotient.mk ((D *ᵥ abelian₂ R k Z v) j) : KR R) =
      lamN R Z j.val v + ∑ l ∈ Finset.Ioo j.val n, cntaCoef R k hD j l • lamN R Z l v := by sorry
