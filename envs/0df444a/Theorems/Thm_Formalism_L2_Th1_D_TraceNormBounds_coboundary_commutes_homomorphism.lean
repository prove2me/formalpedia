-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_coboundary_commutes_homomorphism
-- name    : Formalism.L2.Th1.D.TraceNormBounds.coboundary_commutes_homomorphism
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:57:38.614806+00:00
-- url     : https://prove2.me/theorems/12b0c88e-17db-412d-9c6d-aa8a939daaf9
-- title:
--   Trace Norm Bounds: coboundary commutes homomorphism
-- statement:
--   The Trace Norm Bounds construction uses the coboundary commutes homomorphism property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/CoboundaryCommutesHomomorphism.lean#L150-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/CoboundaryCommutesHomomorphism.lean#L150-L190

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog frobVar)
open MvPowerSeries
open Formalism.L2.Th1.D.TraceNormBounds
variable {K : Type} [Field K]

theorem Formalism.L2.Th1.D.TraceNormBounds.coboundary_commutes_homomorphism {F FE : MvPowerSeries (Fin 2) K} {θ : PowerSeries K}
    (hF0 : constantCoeff F = 0) (hFE0 : constantCoeff FE = 0) (h : IsHom F FE θ)
    (H : MvPowerSeries (Fin 2) K) :
    d1 F (subst ![at1 (0 : Fin 2) θ, at1 (1 : Fin 2) θ] H) =
      subst ![at1 (0 : Fin 3) θ, at1 (1 : Fin 3) θ, at1 (2 : Fin 3) θ] (d1 FE H) := by sorry
