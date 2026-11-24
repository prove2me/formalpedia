-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_rho_eq_trn
-- name    : Formalism.FourierDecayAlt.P.BetaSesquilinearity.rho_eq_trn
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:29:54.40081+00:00
-- url     : https://prove2.me/theorems/68f079cc-5128-4cb4-93be-773b9cacfdc7
-- title:
--   Beta Sesquilinearity: rho eq trn
-- statement:
--   The Beta Sesquilinearity construction uses the rho eq trn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaSesquilinearity.lean#L963-L969
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaSesquilinearity.lean#L963-L969

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.BetaSesquilinearity.rho_eq_trn (D : RealPlaceData k r Wp Wq) (p : SS k r) (F : Mat k r → (Wq →L[ℂ] Wp)) :
    rho D p F = trn (Lp D p) ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹) (Matrix.of p.2.2 * Matrix.of p.2.1) F := by sorry
