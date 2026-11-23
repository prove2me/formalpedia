-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_exists_ne_zero_hom
-- name    : Formalism.IrreducibleCountingLemmas.Z.BN.exists_ne_zero_hom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:02.406373+00:00
-- url     : https://prove2.me/theorems/aadb64fc-8187-4b67-af27-c8cf85ec8e02
-- title:
--   BN: exists ne zero hom
-- statement:
--   The BN construction uses the exists ne zero hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbittAlg.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbittAlg.lean#L32-L34

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit
import Definitions.Def_Lemmata_GeneralBFactSecondVersion_Imports
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z Formalism.IrreducibleCountingLemmas.Z.BN
variable {k A : Type} [Field k] [Ring A] [Algebra k A]
variable {V W S : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
  [AddCommGroup S] [Module A S]

theorem Formalism.IrreducibleCountingLemmas.Z.BN.exists_ne_zero_hom [FiniteDimensional k W] [IsSemisimpleModule A W] [IsSimpleModule A S]
    (h : ∀ a : A, (∀ w : W, a • w = 0) → ∀ s : S, a • s = 0) : ∃ f : W →ₗ[A] S, f ≠ 0 := by sorry
