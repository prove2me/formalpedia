-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_excSum_leOf
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.excSum_leOf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:33.362839+00:00
-- url     : https://prove2.me/theorems/561ba8f9-7c41-4f6b-bb49-db2bcc3bde3d
-- title:
--   Supply AP: exc Sum le Of
-- statement:
--   The Supply AP construction uses the exc Sum le Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffPsi.lean#L62-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffPsi.lean#L62-L81

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcTerm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffPsi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ZeroFreeDirichlet
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP

theorem Formalism.HermitianLattices.Ext.SupplyAP.excSum_leOf {ι : Type*} [Fintype ι] (B : ι → Finset ℝ) (f : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hcard : ∀ i, (B i).card ≤ 1) (huniq : ∀ i j, (B i).Nonempty → (B j).Nonempty → i = j)
    (hf : ∀ i, ∀ β ∈ B i, f β ≤ M) : ∑ i, ∑ β ∈ B i, f β ≤ M := by sorry
