-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_pderiv_inr_linearSubst
-- name    : Formalism.CountingSumsFrames.pderiv_inr_linearSubst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:59.210892+00:00
-- url     : https://prove2.me/theorems/1890acf1-6aa5-49af-ac1d-1c0bd5dbb791
-- title:
--   Counting Sums Frames: pderiv inr linear Subst
-- statement:
--   The Counting Sums Frames construction uses the pderiv inr linear Subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L315-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L315-L322

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

theorem Formalism.CountingSumsFrames.pderiv_inr_linearSubst (g : GL (Fin k) K) (j : Fin k) (f : PolXY K k) :
    pderiv (Sum.inr j) (glAct g f) =
      ∑ i : Fin k, C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i) * glAct g (pderiv (Sum.inr i) f) := by sorry
