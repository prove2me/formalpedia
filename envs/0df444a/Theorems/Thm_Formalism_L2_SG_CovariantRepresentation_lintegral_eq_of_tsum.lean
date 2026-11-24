-- Prove2me | Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_lintegral_eq_of_tsum
-- name    : Formalism.L2.SG.CovariantRepresentation.lintegral_eq_of_tsum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:56.071126+00:00
-- url     : https://prove2.me/theorems/e2e87ca2-66e8-4257-ae99-c14868b91146
-- title:
--   Covariant Representation: lintegral eq of tsum
-- statement:
--   The Covariant Representation construction uses the lintegral eq of tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IsMulRightInvariantOfLattice.lean#L72-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IsMulRightInvariantOfLattice.lean#L72-L91

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IsMulRightInvariantOfLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Set Filter Topology
open scoped ENNReal NNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.CovariantRepresentation
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

theorem Formalism.L2.SG.CovariantRepresentation.lintegral_eq_of_tsum (μ : Measure H) [μ.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ]
    {f g : H → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hf1 : ∀ x, ∑' γ : Γ, f ((γ : H) * x) = 1) (hg1 : ∀ x, ∑' γ : Γ, g ((γ : H) * x) = 1) :
    ∫⁻ x, f x ∂μ = ∫⁻ x, g x ∂μ := by sorry
