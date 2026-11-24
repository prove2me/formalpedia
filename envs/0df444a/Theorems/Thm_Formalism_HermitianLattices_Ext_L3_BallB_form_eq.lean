-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_form_eq
-- name    : Formalism.HermitianLattices.Ext.L3.BallB.form_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:45:26.518838+00:00
-- url     : https://prove2.me/theorems/2358bb4e-62fa-4e2e-b4ee-05f329923149
-- title:
--   Ball B: form eq
-- statement:
--   The Ball B construction uses the form eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOrthBasisMem.lean#L28-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOrthBasisMem.lean#L28-L39

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormSpanSingletonEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLand
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthBasisMem
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
omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.BallB.form_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis ι K V)
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) (x : V) :
    h x x = ∑ i, star (b.repr x i) * b.repr x i * h (b i) (b i) := by sorry
