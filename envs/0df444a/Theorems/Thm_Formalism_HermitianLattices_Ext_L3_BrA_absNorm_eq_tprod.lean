-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_absNorm_eq_tprod
-- name    : Formalism.HermitianLattices.Ext.L3.BrA.absNorm_eq_tprod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:08.741705+00:00
-- url     : https://prove2.me/theorems/3e62c0d8-fb96-40b4-98c0-c1e9de798c66
-- title:
--   Br A: abs Norm eq tprod
-- statement:
--   The Br A construction uses the abs Norm eq tprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FinrankRingOfIntegers.lean#L29-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FinrankRingOfIntegers.lean#L29-L48

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module IsDedekindDomain Function
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BrA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.HermitianLattices.Ext.L3.BrA.absNorm_eq_tprod {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    (Ideal.absNorm I : ℝ) = ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
      (Ideal.absNorm 𝔭.1 : ℝ) ^ sSup {e : ℕ | I ≤ 𝔭.1 ^ e} := by sorry
