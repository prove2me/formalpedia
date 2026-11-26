-- Prove2me | Theorems.Thm_Eden_normalized_first_two_nonneg_of_radii
-- name    : Eden.normalized_first_two_nonneg_of_radii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:59:48.749906+00:00
-- url     : https://prove2.me/theorems/0b424483-0354-5802-a3d6-5a3ab3f95896
-- title:
--   Eden: normalized first two nonneg of radii
-- statement:
--   The Eden construction uses the normalized first two nonneg of radii property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L121-L131
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L121-L131

import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_EventualDimensionFormulas
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.normalized_first_two_nonneg_of_radii (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) (hs₁ : 1 ≤ radiusSq₁ p)
    (hs₂ : 1 ≤ radiusSq₂ p) (i : Fin 5) (hi : i.val < 2) :
    0 ≤ normalizedLogSingularValues c t p i := by sorry
