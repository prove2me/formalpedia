-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_LT_span_short_of_dual
-- name    : Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT.span_short_of_dual
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:58:25.695965+00:00
-- url     : https://prove2.me/theorems/09179cb0-a3cb-4863-b821-c970c0d41548
-- title:
--   LT: span short of dual
-- statement:
--   The LT construction uses the span short of dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL4/PLemTGeo.lean#L41-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL4/PLemTGeo.lean#L41-L51

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Transference
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceCover
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL4_PLemTGeo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open scoped InnerProductSpace
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.TraceIntegrality Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT

theorem Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT.span_short_of_dual {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (Λ : Submodule ℤ W) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (lam : ℝ) (hlam : 0 < lam)
    (hd : ∀ y : W, y ≠ 0 → (∀ x ∈ Λ, ∃ n : ℤ, ⟪x, y⟫_ℝ = (n : ℝ)) → lam ≤ ‖y‖) :
    Submodule.span ℝ {l : W | l ∈ Λ ∧ ‖l‖ ≤ 3 * ((finrank ℝ W : ℝ) / 2 / lam + 1)} = ⊤ := by sorry
