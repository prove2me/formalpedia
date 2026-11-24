-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_LT_span_short_of_cover
-- name    : Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT.span_short_of_cover
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:59:14.779862+00:00
-- url     : https://prove2.me/theorems/36fc3096-52aa-4711-926c-30623e4ec983
-- title:
--   LT: span short of cover
-- statement:
--   The LT construction uses the span short of cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL4/PLemTGeo.lean#L12-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL4/PLemTGeo.lean#L12-L39

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

theorem Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT.span_short_of_cover {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (Λ : Submodule ℤ W) (μ : ℝ) (hμ : 0 < μ) (hcov : ∀ x : W, ∃ l ∈ Λ, ‖x - l‖ ≤ μ) :
    Submodule.span ℝ {l : W | l ∈ Λ ∧ ‖l‖ ≤ 3 * μ} = ⊤ := by sorry
