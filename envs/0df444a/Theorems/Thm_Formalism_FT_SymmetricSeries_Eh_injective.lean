-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_Eh_injective
-- name    : Formalism.FT.SymmetricSeries.Eh_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:25.118874+00:00
-- url     : https://prove2.me/theorems/070349b5-4b55-4a1b-95d9-bde5cc64ff73
-- title:
--   Symmetric Series: Eh injective
-- statement:
--   The Symmetric Series construction uses the Eh injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L218-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L218-L223

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

theorem Formalism.FT.SymmetricSeries.Eh_injective : Function.Injective (Eh R n) := by sorry
