-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_coeff_Fm
-- name    : Formalism.FT.SymmetricSeries.coeff_Fm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:28.251214+00:00
-- url     : https://prove2.me/theorems/a26a9dff-ccf2-4685-9ec6-8c0fac17448b
-- title:
--   Symmetric Series: coeff Fm
-- statement:
--   The Symmetric Series construction uses the coeff Fm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L337-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L337-L350

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

theorem Formalism.FT.SymmetricSeries.coeff_Fm (F : MvPowerSeries (Fin n) R) (m : ℕ) (d : Fin n →₀ ℕ) :
    MvPolynomial.coeff d (Fm F m) = if d.degree = m then MvPowerSeries.coeff d F else 0 := by sorry
