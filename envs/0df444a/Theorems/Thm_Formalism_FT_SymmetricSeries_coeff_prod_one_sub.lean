-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_coeff_prod_one_sub
-- name    : Formalism.FT.SymmetricSeries.coeff_prod_one_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:40.006707+00:00
-- url     : https://prove2.me/theorems/2ac1d3e8-88b5-4c0a-acb2-8203dd0807f7
-- title:
--   Symmetric Series: coeff prod one sub
-- statement:
--   The Symmetric Series construction uses the coeff prod one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L65-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L65-L86

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

theorem Formalism.FT.SymmetricSeries.coeff_prod_one_sub (i : ℕ) :
    coeff i (∏ j : σ, (1 - C (MvPolynomial.X j : MvPolynomial σ R) * X)) =
      (-1) ^ i * MvPolynomial.esymm σ R i := by sorry
