-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_RamifiedLatticeOperators_IndexDeterminantCharacterSums_card_slice
-- name    : Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums.card_slice
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:59:51.499805+00:00
-- url     : https://prove2.me/theorems/f38b5e20-f095-41d1-891b-c7958d242ad6
-- title:
--   Index Determinant Character Sums: card slice
-- statement:
--   The Index Determinant Character Sums construction uses the card slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/InvariantKernelTraceVanishes.lean#L377-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/InvariantKernelTraceVanishes.lean#L377-L392

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_AffineFibreCountComparison
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_InvariantKernelTraceVanishes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedLatticeOperators Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
open Module Finset Matrix
variable {F : Type} [Field F] [Fintype F]

theorem Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums.card_slice {V W : Type} [AddCommGroup V] [Module F V] [Finite V] [AddCommGroup W]
    [Module F W] (L : V →ₗ[F] W) (ψ : V →ₗ[F] F) (s : V) (hs : L s = 0) (hψ : ψ s ≠ 0) (c : F) :
    Fintype.card F * Nat.card {x : V // L x = 0 ∧ ψ x = c} = Nat.card {x : V // L x = 0} := by sorry
