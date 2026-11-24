-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_fourier_eq_down_comp_gauss
-- name    : Formalism.LogVandermondeBounds.product_first_zeroth_parts.fourier_eq_down_comp_gauss
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:12.498855+00:00
-- url     : https://prove2.me/theorems/598fc17d-df67-4b82-a8e0-09d321957985
-- title:
--   product first zeroth parts: fourier eq down comp gauss
-- statement:
--   The product first zeroth parts construction uses the fourier eq down comp gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/FourierIsometryOnNormKernel.lean#L115-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/FourierIsometryOnNormKernel.lean#L115-L151

import Definitions.Def_Formalism_LogVandermondeBounds_GaussOperatorProductFormula
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_FourierIsometryOnNormKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset

theorem Formalism.LogVandermondeBounds.product_first_zeroth_parts.fourier_eq_down_comp_gauss : FourierEqDownGauss := by sorry
