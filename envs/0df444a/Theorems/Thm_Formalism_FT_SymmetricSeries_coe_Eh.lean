-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_coe_Eh
-- name    : Formalism.FT.SymmetricSeries.coe_Eh
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:16.855152+00:00
-- url     : https://prove2.me/theorems/4091ee63-1fec-4766-a812-f57871af6fc9
-- title:
--   Symmetric Series: coe Eh
-- statement:
--   The Symmetric Series construction uses the coe Eh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L283-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L283-L295

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

theorem Formalism.FT.SymmetricSeries.coe_Eh (P : MvPolynomial (Fin n) R) :
    ((Eh R n P : MvPolynomial (Fin n) R) : MvPowerSeries (Fin n) R) =
      MvPowerSeries.subst (hv R n) (P : MvPowerSeries (Fin n) R) := by sorry
