-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_exists_G
-- name    : Formalism.FT.SymmetricSeries.exists_G
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:29.629975+00:00
-- url     : https://prove2.me/theorems/f82c57cb-fd54-4751-9a9d-cdf74b00b36a
-- title:
--   Symmetric Series: exists G
-- statement:
--   The Symmetric Series construction uses the exists G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L367-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L367-L384

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

theorem Formalism.FT.SymmetricSeries.exists_G (F : MvPowerSeries (Fin n) R)
    (hF : ∀ π : Equiv.Perm (Fin n),
      F.subst (fun i => (MvPowerSeries.X (π i) : MvPowerSeries (Fin n) R)) = F) :
    ∃ G : MvPowerSeries (Fin n) R, G.subst (hv R n) = F := by sorry
