-- Prove2me | Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_DetPolyApp_S1_mem_OmF
-- name    : Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp.S1_mem_OmF
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:53:15.101066+00:00
-- url     : https://prove2.me/theorems/fdc0261b-3267-4cc0-a5b2-4b838821dff3
-- title:
--   Det Poly App: S1 mem Om F
-- statement:
--   The Det Poly App construction uses the S1 mem Om F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TruncatedSeriesCounting/TruncatedSeriesProofs/LemmaDetPoly.lean#L338-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TruncatedSeriesCounting/TruncatedSeriesProofs/LemmaDetPoly.lean#L338-L339

import Definitions.Def_Formalism_TruncatedSeriesCounting_LemmaDetPoly
import Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_LemmaDetPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical Polynomial
noncomputable section
open Formalism Formalism.TruncatedSeriesCounting Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp
open DetPolyCore
variable {O K Xs : Type*} [CommRing O] [CommRing K] [Algebra O K]

theorem Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp.S1_mem_OmF {T : Subalgebra O (Xs → O)} {m : ℕ} {f : Xs → MvPolynomial (Fin m) K} :
    f ∈ S1 T m ↔ ∀ α, FromT T (fun x => (f x).coeff α) := by sorry
