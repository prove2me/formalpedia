-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_isLatIn_loc
-- name    : Formalism.HermitianLattices.Ext.L3.U0.isLatIn_loc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:53:08.073057+00:00
-- url     : https://prove2.me/theorems/aa1ecbcf-8879-4db6-83cb-47d4f8cdfbaf
-- title:
--   U0: is Lat In loc
-- statement:
--   The U0 construction uses the is Lat In loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomLocFOfVdZero.lean#L21-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomLocFOfVdZero.lean#L21-L47

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsASDOfTuple
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.U0
open WA
omit [FiniteDimensional K V]

theorem Formalism.HermitianLattices.Ext.L3.U0.isLatIn_loc {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {P : Ideal (𝓞 K)}
    (hP : P.IsPrime) : IsLatIn (locRing P) h ⊤ (Formalism.HermitianLatticesTheory.loc (K := K) P L).toAddSubgroup := by sorry
