-- Prove2me | Theorems.Thm_ConnesGreen_exists_original_window_inclusion
-- name    : ConnesGreen.exists_original_window_inclusion
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T14:03:21.264981+00:00
-- url     : https://prove2.me/theorems/f8df4d39-4fd7-451e-a581-c497a80c0b7e
-- title:
--   Original nested Green physical carriers admit a test-preserving linear isometry
-- statement:
--   For $0<t\le T$, the original canonical Green physical spaces admit a complex linear isometry $U:H_t\to H_T$ such that every original admissible test $g$ supported inside $(-t,t)$ satisfies
--   $$U\,\operatorname{sourceEmbed}_t(Lg)=\operatorname{sourceEmbed}_T(Lg).$$
--   The original physical spaces, Dirichlet metric and source representatives are retained. The isometry is constructed from the dense original supported-test family and exact cross-window Gram identities, rather than assumed as a carrier identification. The native original-source adjoint identity then transfers every actual zeta-zero column and both original syntheses across this inclusion.
-- source:
--   monocap-tech/weil native base b019d40205680f9761a4b0a80cbcad56ee1b606b; exact new source modules Connes/CanonicalGreenWindowInclusion.lean, Screening/MarkerCompression.lean and Connes/CanonicalGreenSupportLimit.lean in Connes_Weil_Original_Support_Limit.zip. Both ordered norm limits are proved natively; prescribed critical endpoint identification, support containment, arithmetic lower bounds and RH are not assumed or asserted.

import Definitions.Def_ConnesGreen_canonical_model
import Mathlib.Analysis.Normed.Operator.Extend
open ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped InnerProductSpace

theorem ConnesGreen.exists_original_window_inclusion (t T : ℝ) (ht : 0 < t) (hT : 0 < T) (htT : t ≤ T) :
    ∃ U : Physical t →ₗᵢ[ℂ] Physical T,
      ∀ g : ℝ → ℂ, ∀ hg : SupportedTest t g,
        U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g) := by sorry
