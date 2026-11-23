-- Prove2me | Theorems.Thm_Formalism_HN_rscMap_apply
-- name    : Formalism.HN.rscMap_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:37.200861+00:00
-- url     : https://prove2.me/theorems/3e87fa69-44a2-4eec-9c7a-16f90a31324f
-- title:
--   HN: rsc Map apply
-- statement:
--   The HN construction uses the rsc Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/RescaleCovol.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/RescaleCovol.lean#L19-L22

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

theorem Formalism.HN.rscMap_apply {P ι : Type*} [Fintype P] [Fintype ι] (c : P → ℝ)
    (x : EuclideanSpace ℝ (P × ι × Fin 2)) (p : P × ι × Fin 2) :
    rscMap c x p = (c p.1)⁻¹ * x p := by sorry
