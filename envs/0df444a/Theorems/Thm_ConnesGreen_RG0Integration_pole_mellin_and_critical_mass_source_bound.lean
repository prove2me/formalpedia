-- Prove2me | Theorems.Thm_ConnesGreen_RG0Integration_pole_mellin_and_critical_mass_source_bound
-- name    : ConnesGreen.RG0Integration.pole_mellin_and_critical_mass_source_bound
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T22:38:49.004974+00:00
-- url     : https://prove2.me/theorems/789191b6-bcc6-4d9e-913b-e9dce37061c1
-- title:
--   Original pole transforms and critical Mellin mass controlled in the physical source metric
-- statement:
--   For $t>0$ and an original smooth test supported in $(-t,t)$, $$|\widehat g(0)|^2+|\widehat g(1)|^2+\int_{\mathbb R}|\widehat g(\tfrac12+ir)|^2\,dr\le(16t^2e^t+8\pi)\|\operatorname{sourceEmbed}_t(Lg)\|^2.$$ This combines the existing supported Dirichlet Mellin bound, exact $2\pi$ mass normalization and original completed-carrier norm identity. It controls the original pole transforms and continuum mass without asserting the sign of the full Weil form.
-- source:
--   monocap-tech/weil: WeilDefect/Connes/RG0DependencyIntegration.lean, original actor and metric adapters at 4ba3a3a569d72a0d5af2ba6ea320f948030dcca5; proof and statement boundaries recovered with Lean elaborator metadata.

import Theorems.Thm_ConnesGreen_supported_mellin_norm_sq_dirichlet_bound
import Theorems.Thm_ConnesGreen_critical_mellin_mass_identity
import Theorems.Thm_ConnesGreen_actual_physical_test_norm
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section

theorem ConnesGreen.RG0Integration.pole_mellin_and_critical_mass_source_bound (t : ℝ) (ht : 0 < t)
    (g : ℝ → ℂ) (hg : SupportedTest t g) :
    ‖mellinHat g 0‖ ^ 2 + ‖mellinHat g 1‖ ^ 2 +
      (∫ r : ℝ, ‖mellinHat g (1/2 + I*r)‖ ^ 2) ≤
      (16 * t ^ 2 * Real.exp t + 8 * Real.pi) *
        ‖sourceEmbed t (problemOneL g)‖ ^ 2 := by sorry
