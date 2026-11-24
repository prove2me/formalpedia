-- Prove2me | Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeLattice_span_image
-- name    : Formalism.HermiteSiegelSlopes.baseChangeLattice_span_image
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:56.366986+00:00
-- url     : https://prove2.me/theorems/b4fff87f-710c-4363-8e17-d4e0293ff845
-- title:
--   Hermite Siegel Slopes: base Change Lattice span image
-- statement:
--   The Hermite Siegel Slopes construction uses the base Change Lattice span image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L646-L648
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L646-L648

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

theorem Formalism.HermiteSiegelSlopes.baseChangeLattice_span_image (s : Set (ι → F)) :
    bcLat (E := E) (Submodule.span (𝓞 F) s) = Submodule.span (𝓞 E) (bcMap (E := E) '' s) := by sorry
