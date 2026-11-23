-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_toFinsupp_sum
-- name    : Formalism.FT.SymmetricSeries.toFinsupp_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:53.046399+00:00
-- url     : https://prove2.me/theorems/478cf5bd-4333-4614-a26e-73497a781b3a
-- title:
--   Symmetric Series: to Finsupp sum
-- statement:
--   The Symmetric Series construction uses the to Finsupp sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L19-L25

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
variable {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

theorem Formalism.FT.SymmetricSeries.toFinsupp_sum (s : Multiset σ) : ∑ i, Multiset.toFinsupp s i = Multiset.card s := by sorry
