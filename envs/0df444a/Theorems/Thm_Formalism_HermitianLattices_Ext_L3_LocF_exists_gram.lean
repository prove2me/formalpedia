-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_exists_gram
-- name    : Formalism.HermitianLattices.Ext.L3.LocF.exists_gram
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:52:42.812207+00:00
-- url     : https://prove2.me/theorems/889d63d6-d419-49f1-816a-f238ac577af3
-- title:
--   Loc F: exists gram
-- statement:
--   The Loc F construction uses the exists gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/VdEqZeroOfNotLe.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/VdEqZeroOfNotLe.lean#L22-L31

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.LocF.exists_gram {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {n : ℕ} (x : Fin n → V) (hx : ∀ i, x i ∈ L) :
    ∃ g : Matrix (Fin n) (Fin n) (𝓞 K), (∀ i j, algebraMap (𝓞 K) K (g i j) = h (x i) (x j)) ∧
      algebraMap (𝓞 K) K g.det = (Matrix.of fun i j => h (x i) (x j)).det := by sorry
