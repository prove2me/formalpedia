-- Prove2me | Theorems.Thm_Formalism_L2_Col_lamGen_diagEmb
-- name    : Formalism.L2.Col.lamGen_diagEmb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:17.187076+00:00
-- url     : https://prove2.me/theorems/98255ebb-437f-420b-a2f1-45188992f84e
-- title:
--   Col: lam Gen diag Emb
-- statement:
--   The Col construction uses the lam Gen diag Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L742-L763
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L742-L763

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]

theorem Formalism.L2.Col.lamGen_diagEmb (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {s a : ℕ} (h : s ≤ n) (ha : a ≤ s) (bl : List ℕ) (S : Finset ℕ)
    (hs : ∀ i : ℕ, s ≤ i → bl.length < coarse a bl i) (g : ↥(uniUT s κ a bl)) :
    lamGen ψ χ n a bl S ⟨diagEmb κ h g.1, diagEmb_mem_uniUT h g.2⟩ = lamGen ψ χ s a bl S g := by sorry
