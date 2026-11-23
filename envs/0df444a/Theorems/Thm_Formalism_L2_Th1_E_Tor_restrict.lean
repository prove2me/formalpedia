-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Tor_restrict
-- name    : Formalism.L2.Th1.E.Tor.restrict
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:10.118961+00:00
-- url     : https://prove2.me/theorems/e5866f0c-db22-4e83-a182-67a560d09a3a
-- title:
--   Tor: restrict
-- statement:
--   The Tor construction uses the restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Taylor0ConstMul.lean#L77-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Taylor0ConstMul.lean#L77-L94

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Taylor0ConstMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.F (opU sgStar th0 taylor0)
open Formalism.L2.Th1.B (fExp fLog)
open Formalism.L2.Th1.E.Tor
variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
open Classical

theorem Formalism.L2.Th1.E.Tor.restrict (hS : AnalyticSys) (hA : PtOfAdd) (hZ : PtOfZero) (hI : PtOfInt)
    (hW : IntCurve (curveL l L ι)) (t : ℂ) (N : ℕ) (hN : 0 < N) (hlN : ¬ l ∣ N)
    (hNt : (N : ℂ) * t ∈ L.lattice) :
    IntPts (curveL l L ι) ((piOf l L ι hA).comp (AddSubgroup.zmultiples t).subtype) ∧
    IsTransSys (curveL l L ι) ((piOf l L ι hA).comp (AddSubgroup.zmultiples t).subtype)
      (fun s : AddSubgroup.zmultiples t => gT l L ι (s : ℂ)) := by sorry
