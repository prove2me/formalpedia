-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_mem_Aw
-- name    : Formalism.FT.SymmetricSeries.mem_Aw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:43.99495+00:00
-- url     : https://prove2.me/theorems/3c9ad0c5-6327-4614-b6a3-cffab91b656a
-- title:
--   Symmetric Series: mem Aw
-- statement:
--   The Symmetric Series construction uses the mem Aw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L390-L401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L390-L401

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

theorem Formalism.FT.SymmetricSeries.mem_Aw (m : ℕ) (α : Fin n →₀ ℕ) : α ∈ Aw n m ↔ wt α = m := by sorry
