-- Prove2me | Theorems.Thm_Formalism_ThetaLiftIndependence_DeterminantSwapLemmas_equiv_apply
-- name    : Formalism.ThetaLiftIndependence.DeterminantSwapLemmas.equiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:54.981025+00:00
-- url     : https://prove2.me/theorems/9365a978-ebd4-4a01-9877-36070dd73aea
-- title:
--   Determinant Swap Lemmas: equiv apply
-- statement:
--   The Determinant Swap Lemmas construction uses the equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/DetSwap.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/DetSwap.lean#L52-L53

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_DetSwap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ThetaLiftIndependence
open Formalism.ThetaLiftIndependence.DeterminantSwapLemmas
variable {𝕜 E F : Type} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

theorem Formalism.ThetaLiftIndependence.DeterminantSwapLemmas.equiv_apply (T : E →ₗ[𝕜] F) (x : (LinearMap.ker T)ᗮ) :
    ((equiv T x : (LinearMap.ker (LinearMap.adjoint T))ᗮ) : F) = T x := by sorry
