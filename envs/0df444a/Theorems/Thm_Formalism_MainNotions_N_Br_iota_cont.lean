-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_Br_iota_cont
-- name    : Formalism.MainNotions.N.Br.iota_cont
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:50:06.322279+00:00
-- url     : https://prove2.me/theorems/3b7c9d1a-e0c7-4cb0-b1ac-f8842332e2b9
-- title:
--   Br: iota cont
-- statement:
--   The Br construction uses the iota cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/QuotientHomNonvanishingBound.lean#L821-L821
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/QuotientHomNonvanishingBound.lean#L821-L821

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

theorem Formalism.MainNotions.N.Br.iota_cont : Continuous (iota nbr i w hw) := by sorry
