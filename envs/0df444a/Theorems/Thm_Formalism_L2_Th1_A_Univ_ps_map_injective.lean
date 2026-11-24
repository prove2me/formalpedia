-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Univ_ps_map_injective
-- name    : Formalism.L2.Th1.A.Univ.ps_map_injective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:16.668961+00:00
-- url     : https://prove2.me/theorems/14dcd5d5-02bf-495d-bf55-6650cb835def
-- title:
--   Univ: ps map injective
-- statement:
--   The Univ construction uses the ps map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L45-L51

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Univ

theorem Formalism.L2.Th1.A.Univ.ps_map_injective {A : Type*} {B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) : Function.Injective (PowerSeries.map f) := by sorry
