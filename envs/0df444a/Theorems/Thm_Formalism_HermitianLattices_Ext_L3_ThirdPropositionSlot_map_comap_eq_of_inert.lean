-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_ThirdPropositionSlot_map_comap_eq_of_inert
-- name    : Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot.map_comap_eq_of_inert
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:05.352798+00:00
-- url     : https://prove2.me/theorems/67fab38c-cd9d-42f5-9bc5-4c9b2f2f614b
-- title:
--   Third Proposition Slot: map comap eq of inert
-- statement:
--   The Third Proposition Slot construction uses the map comap eq of inert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountExtP.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountExtP.lean#L27-L32

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountExtP
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot.map_comap_eq_of_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) :
    extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P := by sorry
