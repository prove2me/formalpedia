-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx4_orbJ_smul_ae
-- name    : Formalism.FourierDecayAlt.P.TBBx4.orbJ_smul_ae
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:59:44.559879+00:00
-- url     : https://prove2.me/theorems/94931162-06c8-5cb5-affb-5ebaa7781e78
-- title:
--   TBBx4: orb J smul ae
-- statement:
--   The TBBx4 construction uses the orb J smul ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L98-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L98-L120

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularityAtPlaceOfSubadditive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx4
open MeasureTheory Filter Topology Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB
open scoped ENNReal ComplexConjugate
noncomputable section
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem Formalism.FourierDecayAlt.P.TBBx4.orbJ_smul_ae {k r : ℕ} (Ds : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (μR : Measure (Mt k r))
    (F G : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℂ) (hc : c ≠ 0)
    (hae : ∀ᵐ q ∂Ds.μSS, D.orbIntegrand Ds γ G q = c • D.orbIntegrand Ds γ F q) :
    D.orbJ Ds γ μR G = c • D.orbJ Ds γ μR F := by sorry
