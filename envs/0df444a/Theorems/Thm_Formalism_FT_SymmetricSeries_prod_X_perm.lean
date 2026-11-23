-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_prod_X_perm
-- name    : Formalism.FT.SymmetricSeries.prod_X_perm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:40.526014+00:00
-- url     : https://prove2.me/theorems/57db2b68-3ac3-4e45-a38a-3adbba7f3079
-- title:
--   Symmetric Series: prod X perm
-- statement:
--   The Symmetric Series construction uses the prod X perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L309-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L309-L318

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

theorem Formalism.FT.SymmetricSeries.prod_X_perm (π : Equiv.Perm (Fin n)) (e : Fin n →₀ ℕ) :
    e.prod (fun s k => (MvPowerSeries.X (π s) : MvPowerSeries (Fin n) R) ^ k) =
      MvPowerSeries.monomial (e.mapDomain π) 1 := by sorry
