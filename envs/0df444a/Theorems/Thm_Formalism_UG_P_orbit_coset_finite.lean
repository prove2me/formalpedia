-- Prove2me | Theorems.Thm_Formalism_UG_P_orbit_coset_finite
-- name    : Formalism.UG.P.orbit_coset_finite
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:52.709612+00:00
-- url     : https://prove2.me/theorems/41ad6b31-44f9-43c8-862e-0c196e1f0720
-- title:
--   P: orbit coset finite
-- statement:
--   The P construction uses the orbit coset finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AssocFin.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AssocFin.lean#L30-L35

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AssocFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G] (K : Subgroup G)

theorem Formalism.UG.P.orbit_coset_finite (hK : IsCommensurated K) (s : G) :
    (MulAction.orbit K ((s : G ⧸ K))).Finite := by sorry
