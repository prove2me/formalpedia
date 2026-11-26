-- Prove2me | Theorems.Thm_Eden_normalizedLogSingularValues_of_stationary_radii
-- name    : Eden.normalizedLogSingularValues_of_stationary_radii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:56:50.583476+00:00
-- url     : https://prove2.me/theorems/39ba96b3-07e2-52ca-a647-65af7b2c1039
-- title:
--   Eden: normalized Log Singular Values of stationary radii
-- statement:
--   The Eden construction uses the normalized Log Singular Values of stationary radii property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L51-L67
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L51-L67

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.normalizedLogSingularValues_of_stationary_radii (c : ℝ) {t : ℝ}
    (ht : 0 < t) (p : PhaseSpace)
    (h₁ : radiusSq₁ p = 0 ∨ radiusSq₁ p = 1 ∨ radiusSq₁ p = 2)
    (h₂ : radiusSq₂ p = 0 ∨ radiusSq₂ p = 1 ∨ radiusSq₂ p = 2) :
    normalizedLogSingularValues c t p =
      descending (radiusPairSpectrum c (radiusSq₁ p) (radiusSq₂ p)) := by sorry
