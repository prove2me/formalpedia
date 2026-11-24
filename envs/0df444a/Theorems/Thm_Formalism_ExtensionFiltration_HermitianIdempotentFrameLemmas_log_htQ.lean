-- Prove2me | Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_log_htQ
-- name    : Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.log_htQ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:06.626645+00:00
-- url     : https://prove2.me/theorems/8892222c-c57e-49b9-b7d5-a1d8d72760be
-- title:
--   Hermitian Idempotent Frame Lemmas: log ht Q
-- statement:
--   The Hermitian Idempotent Frame Lemmas construction uses the log ht Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/GoodBadCut.lean#L340-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/GoodBadCut.lean#L340-L362

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
open Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.log_htQ (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (L S : Submodule (𝓞 K) V) (hL : L.FG) (hS : S.FG) (hsat : IsSat (Formalism.HermitianLatticesTheory.realize b X) L S)
    (hpos : 0 < htQ b X L S) :
    Real.log (htQ b X L S) = Real.log (ht b X L) - Real.log (ht b X S) := by sorry
