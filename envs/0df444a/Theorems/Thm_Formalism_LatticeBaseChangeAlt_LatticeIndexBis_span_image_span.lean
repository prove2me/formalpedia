-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_LatticeIndexBis_span_image_span
-- name    : Formalism.LatticeBaseChangeAlt.LatticeIndexBis.span_image_span
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:51:46.042687+00:00
-- url     : https://prove2.me/theorems/b73cca32-cd60-41af-9de3-e4f6873b8d08
-- title:
--   Lattice Index Bis: span image span
-- statement:
--   The Lattice Index Bis construction uses the span image span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LatticeIndexBis.lean#L40-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LatticeIndexBis.lean#L40-L52

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LatticeIndexBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open Formalism.LatticeBaseChangeAlt.LatticeIndexBis

theorem Formalism.LatticeBaseChangeAlt.LatticeIndexBis.span_image_span {R S M N : Type} [Ring R] [Ring S] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] (g : M →+ N) (φ : R → S) (h : ∀ r x, g (r • x) = φ r • g x)
    (s : Set M) :
    Submodule.span S (g '' (Submodule.span R s : Set M)) = Submodule.span S (g '' s) := by sorry
