-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_Fk_value
-- name    : Formalism.L2.S.Pv.EnergyAbs.Fk_value
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:24:55.831715+00:00
-- url     : https://prove2.me/theorems/7a15eff9-1670-5a38-a809-6aef8029aeb7
-- title:
--   Energy Abs: Fk value
-- statement:
--   The Energy Abs construction uses the Fk value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsFolnerLim.lean#L119-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsFolnerLim.lean#L119-L146

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerLim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem Formalism.L2.S.Pv.EnergyAbs.Fk_value {μ : Measure G} [μ.IsMulLeftInvariant] {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {d : ℝ}
    (hd : 0 < d) {w : HH} {S : Set G} {μS ν : Measure G} [SFinite μS] [SFinite ν] (hq : IsQuot μ μS ν)
    {τ : G → (V →L[ℂ] V)} {W : G → V} (hW : IsWAbs μ σ d w S τ ν W)
    (hΦ : Integrable (fun x : G × G × G => Fk σ w W x.1 x.2.1 x.2.2) (ν.prod (ν.prod μS))) :
    ∫ x, Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)) = ((1 / d : ℝ) : ℂ) := by sorry
