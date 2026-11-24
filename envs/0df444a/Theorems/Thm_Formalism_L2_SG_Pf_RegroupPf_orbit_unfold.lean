-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RegroupPf_orbit_unfold
-- name    : Formalism.L2.SG.Pf.RegroupPf.orbit_unfold
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:26.542131+00:00
-- url     : https://prove2.me/theorems/20650359-e77d-4006-a2c3-13365c80ddc3
-- title:
--   Regroup Pf: orbit unfold
-- statement:
--   The Regroup Pf construction uses the orbit unfold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RegroupPfUnfold.lean#L39-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RegroupPfUnfold.lean#L39-L236

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RegroupPfUnfold
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
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RegroupPf
variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]

theorem Formalism.L2.SG.Pf.RegroupPf.orbit_unfold (μ : Measure H) [μ.IsMulLeftInvariant]
    (N : Subgroup H) [Countable N] {C : Type*} [Countable C] (act : N → C → C) (h1 : ∀ c, act 1 c = c)
    (hmul : ∀ n m c, act (n * m) c = act n (act m c))
    (F : C → H → ℂ) (hFm : ∀ c, Measurable (F c)) (hFeq : ∀ (n : N) c y, F (act n c) y = F c ((n : H)⁻¹ * y))
    (Ω : Set H) (hΩm : MeasurableSet Ω) (hΩc : ∀ x, ∃ n : N, (n : H) * x ∈ Ω)
    (hΩu : ∀ x ∈ Ω, ∀ n : N, (n : H) * x ∈ Ω → n = 1)
    {J : Type*} (r : J → C) (hcov : ∀ c, ∃ j n, act n (r j) = c) (huniq : ∀ j j' n, act n (r j) = r j' → j = j')
    (ΩJ : J → Set H) (hJm : ∀ j, MeasurableSet (ΩJ j))
    (hJc : ∀ j x, ∃ n : N, act n (r j) = r j ∧ (n : H) * x ∈ ΩJ j)
    (hJu : ∀ j, ∀ x ∈ ΩJ j, ∀ n : N, act n (r j) = r j → (n : H) * x ∈ ΩJ j → n = 1)
    (hint : ∫⁻ y in Ω, ∑' c, ‖F c y‖ₑ ∂μ < ⊤) :
    IntegrableOn (fun y => ∑' c, F c y) Ω μ ∧
      ∫ y in Ω, ∑' c, F c y ∂μ = ∑' j, ∫ y in ΩJ j, F (r j) y ∂μ := by sorry
