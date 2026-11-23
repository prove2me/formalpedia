-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_frac_of_fixed
-- name    : Formalism.HermitianLattices.Ext.L3.U0.exists_frac_of_fixed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:07:28.929798+00:00
-- url     : https://prove2.me/theorems/253179a5-c6b0-4d45-97ef-cec543523068
-- title:
--   U0: exists frac of fixed
-- statement:
--   The U0 construction uses the exists frac of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsFracOfFixed.lean#L52-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsFracOfFixed.lean#L52-L78

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

theorem Formalism.HermitianLattices.Ext.L3.U0.exists_frac_of_fixed (hF : IsFixF K F) {P : Ideal (𝓞 K)} (hP : P.IsPrime) {a : K}
    (ha : a ∈ locRing P) (hfix : star a = a) :
    ∃ t s : 𝓞 F, s ∉ P.comap (algebraMap (𝓞 F) (𝓞 K)) ∧ a = toK K t / toK K s := by sorry
