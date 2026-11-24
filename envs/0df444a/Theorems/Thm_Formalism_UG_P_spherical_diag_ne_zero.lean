-- Prove2me | Theorems.Thm_Formalism_UG_P_spherical_diag_ne_zero
-- name    : Formalism.UG.P.spherical_diag_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:36:47.283067+00:00
-- url     : https://prove2.me/theorems/f2f433a3-d53f-4ba7-9b1d-19add625b33a
-- title:
--   P: spherical diag ne zero
-- statement:
--   The P construction uses the spherical diag ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SphericalA.lean#L35-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SphericalA.lean#L35-L41

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SphericalA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.UG
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] {n : ℕ}

theorem Formalism.UG.P.spherical_diag_ne_zero (b : GL (Fin n) L) (hb : (b : Matrix (Fin n) (Fin n) L).BlockTriangular id)
    (i : Fin n) : (b : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by sorry
