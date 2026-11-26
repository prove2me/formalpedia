-- Prove2me | Theorems.Thm_Eden_lyapunovExponent_eq_of_limiting_radii
-- name    : Eden.lyapunovExponent_eq_of_limiting_radii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:57:19.530085+00:00
-- url     : https://prove2.me/theorems/6753a38b-d6d1-4adc-91d2-e33c5ffc70d4
-- title:
--   Eden: lyapunov Exponent eq of limiting radii
-- statement:
--   Either ordering of the two limiting squared radii determines the same ordered
--   spectrum. Squared radius two corresponds to ordinary radius sqrt(2).
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SpectrumTable.lean#L51-L60
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SpectrumTable.lean#L51-L60

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SpectrumTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.lyapunovExponent_eq_of_limiting_radii (c : ℝ) (p : PhaseSpace) {s₁ s₂ : ℝ}
    (h : (limitingSquaredRadius (radiusSq₁ p) = s₁ ∧
        limitingSquaredRadius (radiusSq₂ p) = s₂) ∨
      (limitingSquaredRadius (radiusSq₁ p) = s₂ ∧
        limitingSquaredRadius (radiusSq₂ p) = s₁)) :
    lyapunovExponent c p = descending (radiusPairSpectrum c s₁ s₂) := by sorry
