-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_smul_mem_translateLattice
-- name    : Formalism.CountingSumsFrames.smul_mem_translateLattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:15.891794+00:00
-- url     : https://prove2.me/theorems/b8fa79bf-75d7-4eb7-a5ad-b16cd27af411
-- title:
--   Counting Sums Frames: smul mem translate Lattice
-- statement:
--   The Counting Sums Frames construction uses the smul mem translate Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L376-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L376-L379

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

theorem Formalism.CountingSumsFrames.smul_mem_translateLattice (R : Subring K) (L : Set (PolXY K k)) (hs : ∀ r ∈ R, ∀ f ∈ L, r • f ∈ L) (g : GL (Fin k) K)
    (r : K) (hr : r ∈ R) (f : PolXY K k) (hf : f ∈ latOf g L) : r • f ∈ latOf g L := by sorry
