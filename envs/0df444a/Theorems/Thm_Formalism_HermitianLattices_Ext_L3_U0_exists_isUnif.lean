-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_isUnif
-- name    : Formalism.HermitianLattices.Ext.L3.U0.exists_isUnif
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:21.013792+00:00
-- url     : https://prove2.me/theorems/f4390d3a-3fec-494f-ab1b-7c90167f3a2b
-- title:
--   U0: exists is Unif
-- statement:
--   The U0 construction uses the exists is Unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsFracOfFixed.lean#L80-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsFracOfFixed.lean#L80-L275

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.HermitianLattices.Ext.L3.U0.exists_isUnif (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) :
    ∃ π : K, IsUnif (locRing P) π ∧
      (∀ z ∈ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))), Dv (locRing P) π (algebraMap (𝓞 K) K z)) ∧
      ∀ z : 𝓞 K, Dv (locRing P) π (algebraMap (𝓞 K) K z * π⁻¹) →
        z ∈ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ 2 := by sorry
