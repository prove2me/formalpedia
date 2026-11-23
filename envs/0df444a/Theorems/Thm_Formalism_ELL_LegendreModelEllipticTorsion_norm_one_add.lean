-- Prove2me | Theorems.Thm_Formalism_ELL_LegendreModelEllipticTorsion_norm_one_add
-- name    : Formalism.ELL.LegendreModelEllipticTorsion.norm_one_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:20.928881+00:00
-- url     : https://prove2.me/theorems/071547c9-d2bc-4ddc-90b3-7fb8803b5e2a
-- title:
--   Legendre Model Elliptic Torsion: norm one add
-- statement:
--   The Legendre Model Elliptic Torsion construction uses the norm one add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/Legendre.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/Legendre.lean#L18-L22

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LegendreInvariant
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_Legendre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ELL
open Formalism.ELL.LegendreModelEllipticTorsion
open Polynomial

theorem Formalism.ELL.LegendreModelEllipticTorsion.norm_one_add {K : Type*} [NormedField K] [IsUltrametricDist K] {t : K} (ht : ‖t‖ ≠ 1) :
    ‖1 + t‖ = max 1 ‖t‖ := by sorry
