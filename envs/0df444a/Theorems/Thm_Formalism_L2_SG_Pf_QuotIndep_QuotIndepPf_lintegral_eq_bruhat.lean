-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_QuotIndep_QuotIndepPf_lintegral_eq_bruhat
-- name    : Formalism.L2.SG.Pf.QuotIndep.QuotIndepPf.lintegral_eq_bruhat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:36.98846+00:00
-- url     : https://prove2.me/theorems/b543818c-b00a-4d48-a3f6-a53a1efbff3f
-- title:
--   Quot Indep Pf: lintegral eq bruhat
-- statement:
--   The Quot Indep Pf construction uses the lintegral eq bruhat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/QuotIndepPf.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/QuotIndepPf.lean#L28-L38

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_QuotIndepStmt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CasimirReductionTheory_OneParameterDerivatives_WeilIndicatorMeasures_MeasurableUnitMulIndicator
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_QuotIndepPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.QuotIndep
open Formalism.L2.SG.Pf.QuotIndep.QuotIndepPf
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem Formalism.L2.SG.Pf.QuotIndep.QuotIndepPf.lintegral_eq_bruhat (S : Subgroup G) (μS : Measure S) (μ ν : Measure G) (b : G → ℝ≥0∞)
    (hbm : Measurable b) (hb1 : ∀ x : G, ∫⁻ s, b ((s : G) * x) ∂μS = 1)
    (hν : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f ((s : G) * x) ∂μS ∂ν)
    (f : G → ℝ≥0∞) (hf : Measurable f) (hinv : ∀ (s : S) (x : G), f ((s : G) * x) = f x) :
    ∫⁻ x, f x ∂ν = ∫⁻ x, b x * f x ∂μ := by sorry
