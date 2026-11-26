-- Prove2me | Theorems.Thm_EdenVerified_p22_lyapunovExponent_eq_radiusPairSpectrum
-- name    : EdenVerified.p22_lyapunovExponent_eq_radiusPairSpectrum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:49:43.519461+00:00
-- url     : https://prove2.me/theorems/fdf55567-f3f0-49d5-90c6-cc925f86a3df
-- title:
--   Eden Verified: p22 lyapunov Exponent eq radius Pair Spectrum
-- statement:
--   The Eden Verified construction uses the p22 lyapunov Exponent eq radius Pair Spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1700-L1704
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1700-L1704

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p22_lyapunovExponent_eq_radiusPairSpectrum :
    ∀ (c : ℝ) (p : PhaseSpace),
    lyapunovExponent c p = descending (radiusPairSpectrum c
      (limitingSquaredRadius (radiusSq₁ p)) (limitingSquaredRadius (radiusSq₂ p))) := by sorry
