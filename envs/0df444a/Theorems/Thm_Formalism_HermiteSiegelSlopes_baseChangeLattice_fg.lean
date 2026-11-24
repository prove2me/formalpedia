-- Prove2me | Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeLattice_fg
-- name    : Formalism.HermiteSiegelSlopes.baseChangeLattice_fg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:08.126128+00:00
-- url     : https://prove2.me/theorems/174dbc3f-f9ba-4091-b5ee-0902671ac4c8
-- title:
--   Hermite Siegel Slopes: base Change Lattice fg
-- statement:
--   The Hermite Siegel Slopes construction uses the base Change Lattice fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L650-L653
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L650-L653

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open scoped nonZeroDivisors
open IsDedekindDomain
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem Formalism.HermiteSiegelSlopes.baseChangeLattice_fg (M : Submodule (𝓞 F) (ι → F)) (hM : M.FG) : (bcLat (E := E) M).FG := by sorry
