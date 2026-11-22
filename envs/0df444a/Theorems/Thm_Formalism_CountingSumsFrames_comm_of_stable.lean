-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_comm_of_stable
-- name    : Formalism.CountingSumsFrames.comm_of_stable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:37:45.128189+00:00
-- url     : https://prove2.me/theorems/381169ff-0242-4a9c-b019-0b34bcf929d3
-- title:
--   Counting Sums Frames: comm of stable
-- statement:
--   The Counting Sums Frames construction uses the comm of stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1035-L1045
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1035-L1045

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem Formalism.CountingSumsFrames.comm_of_stable (P Q : V →ₗ[K] V) (hP : P ∘ₗ P = P) (hr : ∀ x ∈ LinearMap.range P, Q x ∈ LinearMap.range P)
    (hk : ∀ x ∈ LinearMap.ker P, Q x ∈ LinearMap.ker P) : ∀ x, P (Q x) = Q (P x) := by sorry
