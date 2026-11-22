-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_smul_mem_latOf_dual
-- name    : Formalism.CountingSumsFrames.Har4.smul_mem_latOf_dual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:35:51.070481+00:00
-- url     : https://prove2.me/theorems/92434f65-c3b1-4d96-8a64-9fb5571ec48a
-- title:
--   Har4: smul mem lat Of dual
-- statement:
--   The Har4 construction uses the smul mem lat Of dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L635-L643
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L635-L643

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
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
open Formalism.CountingSumsFrames.Har4
variable {K : Type} [Field K] {k : ℕ}

theorem Formalism.CountingSumsFrames.Har4.smul_mem_latOf_dual (R : Subring K) (g : GL (Fin k) K) {r : K} (hr : r ∈ R) {f : PolXY K k}
    (hf : f ∈ latOf g (DualLat R)) : r • f ∈ latOf g (DualLat R) := by sorry
