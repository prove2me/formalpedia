-- Prove2me | Theorems.Thm_Eden_normalizedLogSingularValues_eq_lyapunovExponent_of_stationary
-- name    : Eden.normalizedLogSingularValues_eq_lyapunovExponent_of_stationary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:29.78555+00:00
-- url     : https://prove2.me/theorems/835cd72b-49bf-4484-8eb7-bf54550e185e
-- title:
--   Eden: normalized Log Singular Values eq lyapunov Exponent of stationary
-- statement:
--   The Eden construction uses the normalized Log Singular Values eq lyapunov Exponent of stationary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L69-L76
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L69-L76

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.normalizedLogSingularValues_eq_lyapunovExponent_of_stationary (c : ℝ)
    {t : ℝ} (ht : 0 < t) (p : PhaseSpace)
    (h₁ : radiusSq₁ p = 0 ∨ radiusSq₁ p = 1 ∨ radiusSq₁ p = 2)
    (h₂ : radiusSq₂ p = 0 ∨ radiusSq₂ p = 1 ∨ radiusSq₂ p = 2) :
    normalizedLogSingularValues c t p = lyapunovExponent c p := by sorry
