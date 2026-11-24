-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_smul_bij
-- name    : Formalism.RepresentationBoundsCohomology.LOC.smul_bij
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:27:46.776545+00:00
-- url     : https://prove2.me/theorems/1d8e5a33-2030-48bb-bc90-7232324366ec
-- title:
--   LOC: smul bij
-- statement:
--   The LOC construction uses the smul bij property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/HOneTorsionFree.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/HOneTorsionFree.lean#L13-L26

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_PropLoc
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_HOneTorsionFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO annih)
open ReciprocityTheory.Gal
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC

theorem Formalism.RepresentationBoundsCohomology.LOC.smul_bij {O V : Type u} [CommRing O] [IsDomain O] [AddCommGroup V] [Module O V]
    [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] (c : O) (hc : c ≠ 0) :
    Function.Bijective fun v : V => c • v := by sorry
