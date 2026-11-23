-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_divPow_mem_fockLattice
-- name    : Formalism.CountingSumsFrames.divPow_mem_fockLattice
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:34.483681+00:00
-- url     : https://prove2.me/theorems/75548070-278a-4859-a8c3-ca7cd17aec59
-- title:
--   Counting Sums Frames: div Pow mem fock Lattice
-- statement:
--   The Counting Sums Frames construction uses the div Pow mem fock Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L434-L436
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L434-L436

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames

theorem Formalism.CountingSumsFrames.divPow_mem_fockLattice {K : Type} [Field K] [CharZero K] {k : ℕ} (R : Subring K) (l : ℕ) (f : PolXY K k)
    (hf : f ∈ FockLat R) : hDiv K k l f ∈ FockLat R ∧ ctrDiv K k l f ∈ FockLat R := by sorry
