-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_coeff_prodpow_eq_zero
-- name    : Formalism.FT.SymmetricSeries.coeff_prodpow_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:17.965441+00:00
-- url     : https://prove2.me/theorems/a0ffd96e-eae0-4d45-beb9-a5cb6ab229fb
-- title:
--   Symmetric Series: coeff prodpow eq zero
-- statement:
--   The Symmetric Series construction uses the coeff prodpow eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L278-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L278-L281

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

theorem Formalism.FT.SymmetricSeries.coeff_prodpow_eq_zero (α d : Fin n →₀ ℕ) (h : wt α ≠ d.degree) :
    MvPowerSeries.coeff d (α.prod (fun j e => hv R n j ^ e)) = 0 := by sorry
