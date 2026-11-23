-- Prove2me | Theorems.Thm_Formalism_HN_PlaceDecomposition_realize_apply
-- name    : Formalism.HN.PlaceDecomposition.realize_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:14.180142+00:00
-- url     : https://prove2.me/theorems/a453ca8d-642e-4205-8a35-09368c2a0c71
-- title:
--   Place Decomposition: realize apply
-- statement:
--   The Place Decomposition construction uses the realize apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L38-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L38-L45

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PlaceDecomposition
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

theorem Formalism.HN.PlaceDecomposition.realize_apply (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V)
    (p : InfinitePlace K × ι × Fin 2) :
    Formalism.HermitianLatticesTheory.realize b X x p =
      if p.2.2 = 0 then (Formalism.HermitianLatticesTheory.fcoord b X p.1 x p.2.1).re else (Formalism.HermitianLatticesTheory.fcoord b X p.1 x p.2.1).im := by sorry
