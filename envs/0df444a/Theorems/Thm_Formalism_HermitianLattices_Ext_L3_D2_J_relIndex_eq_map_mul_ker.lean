-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_J_relIndex_eq_map_mul_ker
-- name    : Formalism.HermitianLattices.Ext.L3.D2.J.relIndex_eq_map_mul_ker
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:54:57.320229+00:00
-- url     : https://prove2.me/theorems/153e0231-18a7-44db-8431-7c61f7ff1666
-- title:
--   J: rel Index eq map mul ker
-- statement:
--   The J construction uses the rel Index eq map mul ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RelIndexEqMapMulKer.lean#L16-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RelIndexEqMapMulKer.lean#L16-L30

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqMapMulKer
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

theorem Formalism.HermitianLattices.Ext.L3.D2.J.relIndex_eq_map_mul_ker {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G →+ G')
    {A B : AddSubgroup G} (hBA : B ≤ A) :
    B.relIndex A = (B.map f).relIndex (A.map f) * (B ⊓ f.ker).relIndex (A ⊓ f.ker) := by sorry
