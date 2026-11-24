-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_cardUni
-- name    : Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.cardUni
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:51.748478+00:00
-- url     : https://prove2.me/theorems/7941c568-f8fd-44fe-ba63-5ea12e36a0cc
-- title:
--   Cumulant Estimates: card Uni
-- statement:
--   The Cumulant Estimates construction uses the card Uni property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HilbertSchmidtHalfBound.lean#L476-L495
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HilbertSchmidtHalfBound.lean#L476-L495

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.CumulantEstimateDefs Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
open Finset

theorem Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.cardUni (F : Type) [Field F] [Fintype F] (r : ℕ) (blk : Fin r → ℕ) :
    Nat.card {A : Matrix (Fin r) (Fin r) F // ∀ i j, blk j ≤ blk i → A i j = if i = j then 1 else 0} =
      Fintype.card F ^ (univ.filter (fun ij : Fin r × Fin r => blk ij.1 < blk ij.2)).card := by sorry
