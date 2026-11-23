-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_coeff_mapDomain_of_symm
-- name    : Formalism.FT.SymmetricSeries.coeff_mapDomain_of_symm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:32.946252+00:00
-- url     : https://prove2.me/theorems/51df01f1-66d7-4e83-9e66-44d48663a75a
-- title:
--   Symmetric Series: coeff map Domain of symm
-- statement:
--   The Symmetric Series construction uses the coeff map Domain of symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L320-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L320-L332

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

theorem Formalism.FT.SymmetricSeries.coeff_mapDomain_of_symm (F : MvPowerSeries (Fin n) R)
    (hF : ∀ π : Equiv.Perm (Fin n),
      F.subst (fun i => (MvPowerSeries.X (π i) : MvPowerSeries (Fin n) R)) = F)
    (π : Equiv.Perm (Fin n)) (d : Fin n →₀ ℕ) :
    MvPowerSeries.coeff (d.mapDomain π) F = MvPowerSeries.coeff d F := by sorry
