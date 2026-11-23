-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_Fm_symm
-- name    : Formalism.FT.SymmetricSeries.Fm_symm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:41.600672+00:00
-- url     : https://prove2.me/theorems/d94e912b-85cb-4903-8032-177e18c62fcd
-- title:
--   Symmetric Series: Fm symm
-- statement:
--   The Symmetric Series construction uses the Fm symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L352-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L352-L365

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

theorem Formalism.FT.SymmetricSeries.Fm_symm (F : MvPowerSeries (Fin n) R)
    (hF : ∀ π : Equiv.Perm (Fin n),
      F.subst (fun i => (MvPowerSeries.X (π i) : MvPowerSeries (Fin n) R)) = F)
    (m : ℕ) : (Fm F m).IsSymmetric := by sorry
