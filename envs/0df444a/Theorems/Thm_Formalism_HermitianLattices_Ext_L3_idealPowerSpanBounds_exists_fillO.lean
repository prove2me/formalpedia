-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_exists_fillO
-- name    : Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.exists_fillO
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:15:52.844718+00:00
-- url     : https://prove2.me/theorems/cae72947-a368-4b7d-be09-f61443acbcc9
-- title:
--   ideal Power Span Bounds: exists fill O
-- statement:
--   The ideal Power Span Bounds construction uses the exists fill O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtPPowLeSpanSup.lean#L163-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtPPowLeSpanSup.lean#L163-L174

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.exists_fillO {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d : 𝓞 F} {c k : ℕ}
    (hd : d ∉ 𝔭 ^ (c + 1)) (hck : c ≤ k) {s : 𝓞 K} (hs : s ∈ extP K 𝔭 ^ k) :
    ∃ r ∈ extP K 𝔭 ^ (k - c), s - ι d * r ∈ extP K 𝔭 ^ (k + 1) := by sorry
