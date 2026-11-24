-- Prove2me | Theorems.Thm_Formalism_ExtensionFiltration_rkK_pos
-- name    : Formalism.ExtensionFiltration.rkK_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:28.386289+00:00
-- url     : https://prove2.me/theorems/d6f1fd9f-2749-4669-a194-90ef2b60fe3d
-- title:
--   Extension Filtration: rk K pos
-- statement:
--   The Extension Filtration construction uses the rk K pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/DescentCut.lean#L13-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/DescentCut.lean#L13-L25

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_DescentCut
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeIntoDivisionHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_DescentCut
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

theorem Formalism.ExtensionFiltration.rkK_pos {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] (b : Basis ι K V)
    (A : Submodule (𝓞 K) V) (hA : A ≠ ⊥) : 0 < rkK (K := K) A := by sorry
