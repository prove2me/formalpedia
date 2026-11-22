-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_pow_log_div_choose_mem
-- name    : Formalism.CountingSumsFrames.pow_log_div_choose_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:45.836908+00:00
-- url     : https://prove2.me/theorems/78cf0bb7-6869-47c5-8afc-4654821bd4d4
-- title:
--   Counting Sums Frames: pow log div choose mem
-- statement:
--   The Counting Sums Frames construction uses the pow log div choose mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L71-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L71-L92

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

theorem Formalism.CountingSumsFrames.pow_log_div_choose_mem {K : Type} [Field K] [CharZero K] (R : Subring K) (p : ℕ) (hp : p.Prime) (hR : PLocal R p)
    (n N l : ℕ) (hn : n ≤ N) : (p : K) ^ Nat.log p N / ((n.choose l : ℕ) : K) ∈ R := by sorry
