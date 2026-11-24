-- Prove2me | Theorems.Thm_Formalism_ThetaLiftIndependence_ChainScalarLemmas_mem
-- name    : Formalism.ThetaLiftIndependence.ChainScalarLemmas.mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:44:30.022188+00:00
-- url     : https://prove2.me/theorems/c8d2fe61-ba33-41ee-b2be-70ea3999737e
-- title:
--   Chain Scalar Lemmas: mem
-- statement:
--   The Chain Scalar Lemmas construction uses the mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/ChainScalar.lean#L17-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/ChainScalar.lean#L17-L30

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

theorem Formalism.ThetaLiftIndependence.ChainScalarLemmas.mem (T : ∀ j, E (j + 1) →ₗ[𝕜] E j) (S : ∀ j, Submodule 𝕜 (E j))
    (hS : ∀ j, ∀ x ∈ S j, LinearMap.adjoint (T j) x ∈ S (j + 1)) :
    ∀ (m : ℕ), ∀ x ∈ S 0, LinearMap.adjoint (downChain T m) x ∈ S m := by sorry
