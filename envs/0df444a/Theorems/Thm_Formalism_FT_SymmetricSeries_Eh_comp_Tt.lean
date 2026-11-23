-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_Eh_comp_Tt
-- name    : Formalism.FT.SymmetricSeries.Eh_comp_Tt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:20.564597+00:00
-- url     : https://prove2.me/theorems/172f79fa-3234-4d19-bf5b-c0ae938339fc
-- title:
--   Symmetric Series: Eh comp Tt
-- statement:
--   The Symmetric Series construction uses the Eh comp Tt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L204-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L204-L210

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
variable (R : Type*) [CommRing R] (n : ℕ)
variable {R n}
variable (R n)
variable {R n}

theorem Formalism.FT.SymmetricSeries.Eh_comp_Tt : (Eh R n).comp (Tt R n) = Ee R n := by sorry
