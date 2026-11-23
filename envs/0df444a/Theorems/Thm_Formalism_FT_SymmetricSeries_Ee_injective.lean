-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_Ee_injective
-- name    : Formalism.FT.SymmetricSeries.Ee_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:46.80826+00:00
-- url     : https://prove2.me/theorems/19727663-1104-442b-8548-3f4930e5f582
-- title:
--   Symmetric Series: Ee injective
-- statement:
--   The Symmetric Series construction uses the Ee injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L189-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L189-L194

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

theorem Formalism.FT.SymmetricSeries.Ee_injective : Function.Injective (Ee R n) := by sorry
