-- Prove2me | Theorems.Thm_Eden_lyapunovExponent_eq_radiusPairSpectrum
-- name    : Eden.lyapunovExponent_eq_radiusPairSpectrum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:47:44.439246+00:00
-- url     : https://prove2.me/theorems/e326bfa0-9c34-555f-92f4-e98460019d50
-- title:
--   Eden: lyapunov Exponent eq radius Pair Spectrum
-- statement:
--   The Eden construction uses the lyapunov Exponent eq radius Pair Spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SpectrumTable.lean#L19-L23
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SpectrumTable.lean#L19-L23

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SpectrumTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.lyapunovExponent_eq_radiusPairSpectrum (c : ℝ) (p : PhaseSpace) :
    lyapunovExponent c p = descending (radiusPairSpectrum c
      (limitingSquaredRadius (radiusSq₁ p)) (limitingSquaredRadius (radiusSq₂ p))) := by sorry
