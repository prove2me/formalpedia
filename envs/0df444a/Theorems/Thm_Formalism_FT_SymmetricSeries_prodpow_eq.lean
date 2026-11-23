-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_prodpow_eq
-- name    : Formalism.FT.SymmetricSeries.prodpow_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:29.685171+00:00
-- url     : https://prove2.me/theorems/257cb532-89cf-4a4b-9875-58a63e539d39
-- title:
--   Symmetric Series: prodpow eq
-- statement:
--   The Symmetric Series construction uses the prodpow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L261-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L261-L269

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

theorem Formalism.FT.SymmetricSeries.prodpow_eq (α : Fin n →₀ ℕ) : α.prod (fun j e => hv R n j ^ e) =
    ((∏ j : Fin n, (MvPolynomial.hsymm (Fin n) R (j + 1)) ^ (α j) : MvPolynomial (Fin n) R) :
      MvPowerSeries (Fin n) R) := by sorry
