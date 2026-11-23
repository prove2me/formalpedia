-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_locF_eq_loc
-- name    : Formalism.HermitianLattices.Ext.L3.locF_eq_loc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:38.512412+00:00
-- url     : https://prove2.me/theorems/69381f4a-0f87-4713-8242-5a16db0683a4
-- title:
--   L3: loc F eq loc
-- statement:
--   The L3 construction uses the loc F eq loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtIffVd.lean#L14-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtIffVd.lean#L14-L38

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
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

theorem Formalism.HermitianLattices.Ext.L3.locF_eq_loc (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (L : Submodule (𝓞 K) V) :
    locF (P.comap (algebraMap (𝓞 F) (𝓞 K))) L = Formalism.HermitianLatticesTheory.loc (K := K) P L := by sorry
