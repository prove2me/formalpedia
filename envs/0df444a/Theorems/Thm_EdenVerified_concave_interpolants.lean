-- Prove2me | Theorems.Thm_EdenVerified_concave_interpolants
-- name    : EdenVerified.concave_interpolants
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:25:40.707822+00:00
-- url     : https://prove2.me/theorems/ee50e32c-94cc-5ee3-8d1c-3c5e631fad41
-- title:
--   Eden Verified: concave interpolants
-- statement:
--   Concavity of the finite-time and limiting interpolants on [0,5].
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L479-L484
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L479-L484

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.concave_interpolants (c : ℝ) (p : PhaseSpace) :
    (∀ t : ℝ, 0 < t → ConcaveOn ℝ (Icc (0 : ℝ) 5) (fun d => Real.log
      (singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d) / t)) ∧
    ConcaveOn ℝ (Icc (0 : ℝ) 5) (spectrumInterpolation (lyapunovExponent c p)) := by sorry
