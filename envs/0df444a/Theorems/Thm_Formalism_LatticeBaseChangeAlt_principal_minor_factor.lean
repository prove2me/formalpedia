-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_principal_minor_factor
-- name    : Formalism.LatticeBaseChangeAlt.principal_minor_factor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:55.03057+00:00
-- url     : https://prove2.me/theorems/725e9c71-1a3a-4f76-9c08-952a791847f6
-- title:
--   Lattice Base Change Alt: principal minor factor
-- statement:
--   The Lattice Base Change Alt construction uses the principal minor factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/DetMulEqSumPrincipal.lean#L125-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/DetMulEqSumPrincipal.lean#L125-L135

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ParameterInequalities
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_DetMulEqSumPrincipal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Finset Matrix Polynomial

theorem Formalism.LatticeBaseChangeAlt.principal_minor_factor {K : Type*} [CommRing K] {i n : ℕ} (A : Matrix (Fin i) (Fin n) K)
    (B : Matrix (Fin n) (Fin i) K) (S : Finset (Fin n)) (hS : S.card = i) :
    ((B * A).submatrix (Subtype.val : S → Fin n) Subtype.val).det
      = (B.submatrix (S.orderEmbOfFin hS) id).det * (A.submatrix id (S.orderEmbOfFin hS)).det := by sorry
