-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_hasSubst_hv
-- name    : Formalism.FT.SymmetricSeries.hasSubst_hv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:50:18.198212+00:00
-- url     : https://prove2.me/theorems/331f95e0-9a42-4abf-b2de-2ece52822c8b
-- title:
--   Symmetric Series: has Subst hv
-- statement:
--   The Symmetric Series construction uses the has Subst hv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L252-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L252-L257

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.FT Formalism.FT.SymmetricSeries
variable {R : Type*} [CommRing R] {n : ℕ}

theorem Formalism.FT.SymmetricSeries.hasSubst_hv : MvPowerSeries.HasSubst (hv R n) := by sorry
