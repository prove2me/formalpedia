-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_J_gram_rel
-- name    : Formalism.HermitianLattices.Ext.L3.D2.J.gram_rel
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T09:54:39.276433+00:00
-- url     : https://prove2.me/theorems/23f5e420-1a20-4702-b0ef-21147a3e1a23
-- title:
--   J: gram rel
-- statement:
--   The J construction uses the gram rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RelIndexEqMapMulKer.lean#L190-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RelIndexEqMapMulKer.lean#L190-L206

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqMapMulKer
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.D2.J

theorem Formalism.HermitianLattices.Ext.L3.D2.J.gram_rel (h : V →ₗ⋆[K] V →ₗ[K] K) {m : ℕ} (a b : Fin m → V) (e : Fin m → K) (γ : K)
    (hab : ∀ i, γ • b i = e i • a i) :
    (star γ * γ) ^ m * (Matrix.of fun i j => h (b i) (b j)).det =
      ((∏ i, star (e i)) * ∏ i, e i) * (Matrix.of fun i j => h (a i) (a j)).det := by sorry
