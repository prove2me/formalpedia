-- Prove2me | Theorems.Thm_Formalism_HN_realize_smul_eq
-- name    : Formalism.HN.realize_smul_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:43.542562+00:00
-- url     : https://prove2.me/theorems/2c9505a1-0df2-4914-9adb-c362b37aca46
-- title:
--   HN: realize smul eq
-- statement:
--   The HN construction uses the realize smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/RescaleCovol.lean#L40-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/RescaleCovol.lean#L40-L72

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RescaleCovol
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
open Formalism Formalism.HN
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

theorem Formalism.HN.realize_smul_eq (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (c : InfinitePlace K → ℝ) (hX : ∀ v, IsUnit (X v).det) (hc : ∀ v, 0 < c v) (x : V) :
    Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v) x = rscMap c (Formalism.HermitianLatticesTheory.realize b X x) := by sorry
