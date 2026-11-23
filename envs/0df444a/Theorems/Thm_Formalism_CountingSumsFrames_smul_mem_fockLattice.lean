-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_smul_mem_fockLattice
-- name    : Formalism.CountingSumsFrames.smul_mem_fockLattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:15.6598+00:00
-- url     : https://prove2.me/theorems/0dd4ec2c-ce23-4bc9-af95-736138f1ee70
-- title:
--   Counting Sums Frames: smul mem fock Lattice
-- statement:
--   The Counting Sums Frames construction uses the smul mem fock Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L211-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L211-L215

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

theorem Formalism.CountingSumsFrames.smul_mem_fockLattice (R : Subring K) (r : K) (hr : r ∈ R) (f : PolXY K k) (hf : f ∈ FockLat R) :
    r • f ∈ FockLat R := by sorry
