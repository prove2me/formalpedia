-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_sumsq_div_eq
-- name    : Formalism.L2.S.Pv.EnergyAbs.sumsq_div_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:16:22.60983+00:00
-- url     : https://prove2.me/theorems/b19568a7-dc22-5336-be7b-71f9b0981b7f
-- title:
--   Energy Abs: sumsq div eq
-- statement:
--   The Energy Abs construction uses the sumsq div eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsFolner.lean#L76-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsFolner.lean#L76-L111

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerConv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerSum
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerLim
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem Formalism.L2.S.Pv.EnergyAbs.sumsq_div_eq {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {w : HH} (hw : ‖w‖ = 1) {S : Set G}
    {μS ν : Measure G} (hS : IsHaarSub S μS) [SFinite ν] {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hWc : Continuous W) (hW1 : ∫⁻ x, ‖W x‖ₑ ∂ν < ⊤) {Ω : Set G} (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S)
    (hfin : μS Ω < ⊤)
    (hint : Integrable (fun x : G × G × G => rat μS Ω x.2.2 • Fk σ w W x.1 x.2.1 x.2.2) (ν.prod (ν.prod μS))) :
    (((∑ i, ‖yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i)‖ ^ 2) / (μS Ω).toReal : ℝ) : ℂ) =
      ∫ x, rat μS Ω x.2.2 • Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)) := by sorry
