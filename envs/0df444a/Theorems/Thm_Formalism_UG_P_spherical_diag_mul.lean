-- Prove2me | Theorems.Thm_Formalism_UG_P_spherical_diag_mul
-- name    : Formalism.UG.P.spherical_diag_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:02.584875+00:00
-- url     : https://prove2.me/theorems/4132d27c-ff1b-4fd8-9445-3508aa4fad27
-- title:
--   P: spherical diag mul
-- statement:
--   The P construction uses the spherical diag mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SphericalA.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SphericalA.lean#L16-L22

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

theorem Formalism.UG.P.spherical_diag_mul (A B : Matrix (Fin n) (Fin n) L) (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin n) : (A * B) i i = A i i * B i i := by sorry
