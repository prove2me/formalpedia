-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_prod_map_X_eq_monomial
-- name    : Formalism.FT.SymmetricSeries.prod_map_X_eq_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:26.728746+00:00
-- url     : https://prove2.me/theorems/aced57e9-a01d-4721-b284-420c9359a812
-- title:
--   Symmetric Series: prod map X eq monomial
-- statement:
--   The Symmetric Series construction uses the prod map X eq monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L10-L17

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

theorem Formalism.FT.SymmetricSeries.prod_map_X_eq_monomial (s : Multiset σ) :
    (s.map (MvPolynomial.X : σ → MvPolynomial σ R)).prod =
      MvPolynomial.monomial (Multiset.toFinsupp s) 1 := by sorry
