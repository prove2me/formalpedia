-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_mem_latOf_iff
-- name    : Formalism.CountingSumsFrames.Har4.mem_latOf_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:30:16.233412+00:00
-- url     : https://prove2.me/theorems/21fab349-25fa-4326-97ce-72b825712adb
-- title:
--   Har4: mem lat Of iff
-- statement:
--   The Har4 construction uses the mem lat Of iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L153-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L153-L159

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

theorem Formalism.CountingSumsFrames.Har4.mem_latOf_iff {K : Type} [Field K] {k : ℕ} (g : GL (Fin k) K) (S : Set (PolXY K k)) (f : PolXY K k) :
    f ∈ latOf g S ↔ glAct g⁻¹ f ∈ S := by sorry
