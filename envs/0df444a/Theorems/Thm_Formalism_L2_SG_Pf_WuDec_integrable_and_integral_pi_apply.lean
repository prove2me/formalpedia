-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_WuDec_integrable_and_integral_pi_apply
-- name    : Formalism.L2.SG.Pf.WuDec.integrable_and_integral_pi_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:48.58411+00:00
-- url     : https://prove2.me/theorems/6cbaad44-ee7a-4daf-a151-a7fbe93a6175
-- title:
--   Wu Dec: integrable and integral pi apply
-- statement:
--   The Wu Dec construction uses the integrable and integral pi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/TensInt.lean#L98-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/TensInt.lean#L98-L144

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_TensInt
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
open scoped InnerProductSpace
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.WuDec

theorem Formalism.L2.SG.Pf.WuDec.integrable_and_integral_pi_apply :
  ∀ (ι : Type) [Fintype ι] (X : ι → Type) [∀ v, MeasurableSpace (X v)] (μ : ∀ v, Measure (X v))
    [∀ v, SigmaFinite (μ v)] (V : ι → Type) [∀ v, NormedAddCommGroup (V v)] [∀ v, InnerProductSpace ℂ (V v)]
    [∀ v, FiniteDimensional ℂ (V v)] (Vπ : Type) [NormedAddCommGroup Vπ] [InnerProductSpace ℂ Vπ]
    [FiniteDimensional ℂ Vπ] (tens : (∀ v, V v) → Vπ),
    (∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) → Submodule.span ℂ (Set.range tens) = ⊤ →
    ∀ G : ∀ v, X v → V v, (∀ v, Integrable (G v) (μ v)) →
      Integrable (fun y : ∀ v, X v => tens (fun v => G v (y v))) (Measure.pi μ) ∧
        ∫ y, tens (fun v => G v (y v)) ∂(Measure.pi μ) = tens (fun v => ∫ t, G v t ∂(μ v)) := by sorry
