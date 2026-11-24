-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_isHermSemilocal_locRing
-- name    : Formalism.HermitianLattices.Ext.L3.WA.isHermSemilocal_locRing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:08:53.142507+00:00
-- url     : https://prove2.me/theorems/11307980-55fe-4423-bf92-afff9e64099c
-- title:
--   WA: is Herm Semilocal loc Ring
-- statement:
--   The WA construction uses the is Herm Semilocal loc Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsHermSemilocalLocRing.lean#L174-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsHermSemilocalLocRing.lean#L174-L180

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapNeZeroOfMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsHermSemilocalLocRing
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.HermitianLattices.Ext.L3.WA.isHermSemilocal_locRing (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)}
    (hp : p.IsMaximal) : IsHermSemilocal (locRing p) := by sorry
