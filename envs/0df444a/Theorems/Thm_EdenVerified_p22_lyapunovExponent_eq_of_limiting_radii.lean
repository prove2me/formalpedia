-- Prove2me | Theorems.Thm_EdenVerified_p22_lyapunovExponent_eq_of_limiting_radii
-- name    : EdenVerified.p22_lyapunovExponent_eq_of_limiting_radii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:49:55.92908+00:00
-- url     : https://prove2.me/theorems/b8663328-172d-4bb9-8114-07543ade46af
-- title:
--   Eden Verified: p22 lyapunov Exponent eq of limiting radii
-- statement:
--   The Eden Verified construction uses the p22 lyapunov Exponent eq of limiting radii property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1721-L1728
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1721-L1728

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p22_lyapunovExponent_eq_of_limiting_radii :
    ∀ (c : ℝ) (p : PhaseSpace) {s₁ s₂ : ℝ}
    (h : (limitingSquaredRadius (radiusSq₁ p) = s₁ ∧
        limitingSquaredRadius (radiusSq₂ p) = s₂) ∨
      (limitingSquaredRadius (radiusSq₁ p) = s₂ ∧
        limitingSquaredRadius (radiusSq₂ p) = s₁)),
    lyapunovExponent c p = descending (radiusPairSpectrum c s₁ s₂) := by sorry
