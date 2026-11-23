-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_coeff_Eh
-- name    : Formalism.FT.SymmetricSeries.coeff_Eh
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:46.784264+00:00
-- url     : https://prove2.me/theorems/58f79f60-7490-40f5-902e-b2a295908812
-- title:
--   Symmetric Series: coeff Eh
-- statement:
--   The Symmetric Series construction uses the coeff Eh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L297-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L297-L301

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

theorem Formalism.FT.SymmetricSeries.coeff_Eh (P : MvPolynomial (Fin n) R) (d : Fin n →₀ ℕ) :
    MvPolynomial.coeff d (Eh R n P) =
      ∑ᶠ α, MvPolynomial.coeff α P • MvPowerSeries.coeff d (α.prod fun j e => hv R n j ^ e) := by sorry
