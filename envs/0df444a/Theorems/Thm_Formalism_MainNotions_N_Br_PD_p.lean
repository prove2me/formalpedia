-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_Br_PD_p
-- name    : Formalism.MainNotions.N.Br.PD_p
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:51:32.381277+00:00
-- url     : https://prove2.me/theorems/c71a5b6d-22da-4d1f-8634-5fc14a935468
-- title:
--   Br: PD p
-- statement:
--   The Br construction uses the PD p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/QuotientHomNonvanishingBound.lean#L817-L817
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/QuotientHomNonvanishingBound.lean#L817-L817

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.WeaklyAdmissibleFiltrations Module
noncomputable section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations Module
open Formalism Formalism.MainNotions Formalism.MainNotions.N
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.N.Br
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
variable {N} (L : LocTheory) (nbr : NBr N) (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E))
  (hw : w ∈ placesOver H.E (N.l i))

theorem Formalism.MainNotions.N.Br.PD_p : (PD L nbr i w hw).p = N.l i := by sorry
