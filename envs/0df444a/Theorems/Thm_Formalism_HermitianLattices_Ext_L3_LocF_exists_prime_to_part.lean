-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_exists_prime_to_part
-- name    : Formalism.HermitianLattices.Ext.L3.LocF.exists_prime_to_part
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:58.151594+00:00
-- url     : https://prove2.me/theorems/f17f6c09-8990-409e-b769-c02807a5f9d2
-- title:
--   Loc F: exists prime to part
-- statement:
--   The Loc F construction uses the exists prime to part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapIntCastSmul.lean#L77-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapIntCastSmul.lean#L77-L94

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
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
variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.HermitianLattices.Ext.L3.LocF.exists_prime_to_part {c : 𝓞 F} (hc : c ≠ 0) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsMaximal) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∀ 𝔮 : Ideal (𝓞 F), 𝔮.IsMaximal → 𝔮 ≠ 𝔭 → ∃ u : 𝓞 F, u ∉ 𝔮 ∧ c ∣ u * t := by sorry
