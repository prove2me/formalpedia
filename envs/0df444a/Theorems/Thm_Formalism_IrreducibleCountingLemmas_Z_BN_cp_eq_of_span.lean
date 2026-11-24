-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_cp_eq_of_span
-- name    : Formalism.IrreducibleCountingLemmas.Z.BN.cp_eq_of_span
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:36.733546+00:00
-- url     : https://prove2.me/theorems/f843763a-4c44-4622-aec2-0d16cc374c31
-- title:
--   BN: cp eq of span
-- statement:
--   The BN construction uses the cp eq of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L304-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L304-L377

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
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

theorem Formalism.IrreducibleCountingLemmas.Z.BN.cp_eq_of_span {K A : Type} [Field K] [IsAlgClosed K] [Ring A] [Algebra K A]
    (Γ : Set A) (hΓ : Submodule.span K Γ = ⊤) (V W : Type) [AddCommGroup V]
    [Module K V] [Module A V] [IsScalarTower K A V] [FiniteDimensional K V] [AddCommGroup W]
    [Module K W] [Module A W] [IsScalarTower K A W] [FiniteDimensional K W]
    (h : ∀ g ∈ Γ, cp K V g = cp K W g) : (cp K V : A → K[X]) = cp K W := by sorry
