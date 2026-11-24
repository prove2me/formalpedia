-- Prove2me | Theorems.Thm_Formalism_UG_P_herm_diag
-- name    : Formalism.UG.P.herm_diag
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:16.319135+00:00
-- url     : https://prove2.me/theorems/2c785894-ef60-452b-9cd1-808794ea1bc8
-- title:
--   P: herm diag
-- statement:
--   The P construction uses the herm diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SignatureExists.lean#L31-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SignatureExists.lean#L31-L55

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Matrix

theorem Formalism.UG.P.herm_diag {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ}
    (hJ : J.IsHermitian) :
    ((hJ.eigenvectorUnitary : Matrix n n ℂ) * diagonal (scal hJ.eigenvalues))ᴴ * J *
        ((hJ.eigenvectorUnitary : Matrix n n ℂ) * diagonal (scal hJ.eigenvalues)) =
      diagonal (fun i => ((hJ.eigenvalues i / |hJ.eigenvalues i| : ℝ) : ℂ)) := by sorry
