-- Prove2me | Theorems.Thm_Formalism_UG_P_easyc_latS_std
-- name    : Formalism.UG.P.easyc_latS_std
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:11:26.121178+00:00
-- url     : https://prove2.me/theorems/a4d891ce-0205-4870-b6db-2fe91916892c
-- title:
--   P: easyc lat S std
-- statement:
--   The P construction uses the easyc lat S std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LevelSubgroupFiniteAdelicStandard.lean#L50-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LevelSubgroupFiniteAdelicStandard.lean#L50-L76

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LevelSubgroupFiniteAdelicStandard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E] {n : Type} [Fintype n]
  [DecidableEq n] (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R)

theorem Formalism.UG.P.easyc_latS_std :
    latS (F := F) R (tensInt (F := F) R (intOE E) S₂) (stdLat (n := n) (A := E) (𝓞 E)) =
      stdLat (n := n) (A := E ⊗[F] R) ↥(tensInt (F := F) R (intOE E) S₂) := by sorry
