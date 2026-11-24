-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_exists_prim
-- name    : Formalism.HermitianLattices.Ext.L3.BallB.exists_prim
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:35.071095+00:00
-- url     : https://prove2.me/theorems/ee73a05e-9b34-4bc8-bd45-580c8145b0ad
-- title:
--   Ball B: exists prim
-- statement:
--   The Ball B construction uses the exists prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapConjO.lean#L133-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapConjO.lean#L133-L185

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K]

theorem Formalism.HermitianLattices.Ext.L3.BallB.exists_prim {J : Type*} [Finite J] (a : J → K) {j₀ : J} (ha : a j₀ ≠ 0) {P : Ideal (𝓞 K)}
    (hP : P ≠ ⊤) :
    ∃ (t : K) (c : J → 𝓞 K), (∀ j, algebraMap (𝓞 K) K (c j) = t * a j) ∧ ∃ j, c j ∉ P := by sorry
