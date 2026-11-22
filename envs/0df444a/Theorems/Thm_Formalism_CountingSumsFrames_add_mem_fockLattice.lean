-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_add_mem_fockLattice
-- name    : Formalism.CountingSumsFrames.add_mem_fockLattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:37:31.438043+00:00
-- url     : https://prove2.me/theorems/bdbb2d2f-726e-4cbc-9366-1c5e2edc0300
-- title:
--   Counting Sums Frames: add mem fock Lattice
-- statement:
--   The Counting Sums Frames construction uses the add mem fock Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L205-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L205-L209

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
variable {K : Type} [Field K] [CharZero K] {k : ℕ}

theorem Formalism.CountingSumsFrames.add_mem_fockLattice (R : Subring K) (f g : PolXY K k) (hf : f ∈ FockLat R) (hg : g ∈ FockLat R) :
    f + g ∈ FockLat R := by sorry
