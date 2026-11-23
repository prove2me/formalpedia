-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_coeff_prod_geom
-- name    : Formalism.FT.SymmetricSeries.coeff_prod_geom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:30.497473+00:00
-- url     : https://prove2.me/theorems/c7afd4b2-52d6-4a78-b4b1-3440ceb43531
-- title:
--   Symmetric Series: coeff prod geom
-- statement:
--   The Symmetric Series construction uses the coeff prod geom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L89-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L89-L95

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
variable {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]
open PowerSeries

theorem Formalism.FT.SymmetricSeries.coeff_prod_geom (k : ℕ) :
    coeff k (∏ j : σ, PowerSeries.mk (fun m => (MvPolynomial.X j : MvPolynomial σ R) ^ m)) =
      MvPolynomial.hsymm σ R k := by sorry
