-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_isUnitIn_div_iff
-- name    : Formalism.HermitianLattices.Ext.L3.WA.isUnitIn_div_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:15:03.765027+00:00
-- url     : https://prove2.me/theorems/c05cf662-cb61-4246-a401-c7e78f9a6f3c
-- title:
--   WA: is Unit In div iff
-- statement:
--   The WA construction uses the is Unit In div iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapNeZeroOfMemHcompl.lean#L138-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapNeZeroOfMemHcompl.lean#L138-L164

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormOneOfPair
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapNeZeroOfMemHcompl
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

theorem Formalism.HermitianLattices.Ext.L3.WA.isUnitIn_div_iff {p : Ideal (𝓞 K)} (hp : p.IsPrime) (r : 𝓞 K) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) :
    IsUnitIn (locRing p) (algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) ↔
      r ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by sorry
