-- Prove2me | Theorems.Thm_Formalism_L2_Col_blkDet_diagEmb
-- name    : Formalism.L2.Col.blkDet_diagEmb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:13.568796+00:00
-- url     : https://prove2.me/theorems/60555a4b-19ec-4cb3-aad7-3b72becdc7f7
-- title:
--   Col: blk Det diag Emb
-- statement:
--   The Col construction uses the blk Det diag Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L715-L740
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L715-L740

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

theorem Formalism.L2.Col.blkDet_diagEmb {s : ℕ} (h : s ≤ n) (β : ℕ → ℕ) (c : ℕ) (hc : ∀ i : ℕ, s ≤ i → β i ≠ c) (g : GL (Fin s) κ)
    (hg : g ∈ btG s κ β) (hg' : diagEmb κ h g ∈ btG n κ β) :
    blkDet n κ β c ⟨diagEmb κ h g, hg'⟩ = blkDet s κ β c ⟨g, hg⟩ := by sorry
