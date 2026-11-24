-- Prove2me | Theorems.Thm_Formalism_ThetaLiftIndependence_ChainScalarLemmas_adjoint_downChain_succ_apply
-- name    : Formalism.ThetaLiftIndependence.ChainScalarLemmas.adjoint_downChain_succ_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:28:58.495803+00:00
-- url     : https://prove2.me/theorems/18dd8753-4070-4da0-ad14-452bed6eb3c3
-- title:
--   Chain Scalar Lemmas: adjoint down Chain succ apply
-- statement:
--   The Chain Scalar Lemmas construction uses the adjoint down Chain succ apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/ChainScalar.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/ChainScalar.lean#L10-L15

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ChainScalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ThetaLiftIndependence
open Formalism.ThetaLiftIndependence.ChainScalarLemmas
variable {𝕜 : Type} [RCLike 𝕜] {E : ℕ → Type} [∀ j, NormedAddCommGroup (E j)]
    [∀ j, InnerProductSpace 𝕜 (E j)] [∀ j, FiniteDimensional 𝕜 (E j)]

theorem Formalism.ThetaLiftIndependence.ChainScalarLemmas.adjoint_downChain_succ_apply (T : ∀ j, E (j + 1) →ₗ[𝕜] E j) (m : ℕ) (x : E 0) :
    LinearMap.adjoint (downChain T (m + 1)) x =
      LinearMap.adjoint (T m) (LinearMap.adjoint (downChain T m) x) := by sorry
