-- Prove2me | solution 1 for dependsOn_mem_iff_exists_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:39:08.925209+00:00
-- url     : https://prove2.me/submissions/2f1634d2-4cad-4246-994f-3b21564307d0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma

set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {A : ι → Set Ω} {N : ι → Finset ι} {x : ι → ℝ} {i j : ι} {S T : Finset ι}
open Finset
theorem _root_.solution {α β : Type*} {t : Set α} {A : Set (α → β)} :
    DependsOn (· ∈ A) t ↔ ∃ B : Set (t → β), A = t.restrict ⁻¹' B :=
  dependsOn_iff_exists_comp
