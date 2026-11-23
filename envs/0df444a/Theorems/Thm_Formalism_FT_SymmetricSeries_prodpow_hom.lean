-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_prodpow_hom
-- name    : Formalism.FT.SymmetricSeries.prodpow_hom
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:38.997793+00:00
-- url     : https://prove2.me/theorems/51939eee-a8d2-404f-b1b0-b0bfa90cc6ca
-- title:
--   Symmetric Series: prodpow hom
-- statement:
--   The Symmetric Series construction uses the prodpow hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L271-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L271-L276

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

theorem Formalism.FT.SymmetricSeries.prodpow_hom (α : Fin n →₀ ℕ) :
    (∏ j : Fin n, (MvPolynomial.hsymm (Fin n) R (j + 1)) ^ (α j)).IsHomogeneous (wt α) := by sorry
