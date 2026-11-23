-- Prove2me | Theorems.Thm_Formalism_FT_SymmetricSeries_hsymm_eq_sum_monomial
-- name    : Formalism.FT.SymmetricSeries.hsymm_eq_sum_monomial
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:07.072149+00:00
-- url     : https://prove2.me/theorems/4fc7fc1d-a2aa-4d3b-a16a-62c258ca573d
-- title:
--   Symmetric Series: hsymm eq sum monomial
-- statement:
--   The Symmetric Series construction uses the hsymm eq sum monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L27-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean#L27-L47

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

theorem Formalism.FT.SymmetricSeries.hsymm_eq_sum_monomial (k : ℕ) :
    MvPolynomial.hsymm σ R k =
      ∑ l ∈ finsuppAntidiag (univ : Finset σ) k, MvPolynomial.monomial l 1 := by sorry
