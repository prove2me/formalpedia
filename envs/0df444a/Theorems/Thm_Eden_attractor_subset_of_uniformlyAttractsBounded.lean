-- Prove2me | Theorems.Thm_Eden_attractor_subset_of_uniformlyAttractsBounded
-- name    : Eden.attractor_subset_of_uniformlyAttractsBounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:16:48.509557+00:00
-- url     : https://prove2.me/theorems/92ff618c-f7ba-51f2-ab1a-055ec3f3c259
-- title:
--   Eden: attractor subset of uniformly Attracts Bounded
-- statement:
--   The Eden construction uses the attractor subset of uniformly Attracts Bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/UniformAttraction.lean#L136-L147
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/UniformAttraction.lean#L136-L147

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_AttractorDistance
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_UniformAttraction
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.attractor_subset_of_uniformlyAttractsBounded {c : ℝ} {C : Set PhaseSpace}
    (hclosed : IsClosed C) (hC : UniformlyAttractsBounded c C) : attractor ⊆ C := by sorry
