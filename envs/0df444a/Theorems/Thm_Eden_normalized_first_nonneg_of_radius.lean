-- Prove2me | Theorems.Thm_Eden_normalized_first_nonneg_of_radius
-- name    : Eden.normalized_first_nonneg_of_radius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:59:44.00411+00:00
-- url     : https://prove2.me/theorems/343b08cb-7aa4-5619-9da4-9ae05963262c
-- title:
--   Eden: normalized first nonneg of radius
-- statement:
--   The Eden construction uses the normalized first nonneg of radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L103-L119
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L103-L119

import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_EventualDimensionFormulas
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.normalized_first_nonneg_of_radius (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor)
    (hs : 1 ≤ radiusSq₁ p ∨ 1 ≤ radiusSq₂ p) :
    0 ≤ normalizedLogSingularValues c t p 0 := by sorry
