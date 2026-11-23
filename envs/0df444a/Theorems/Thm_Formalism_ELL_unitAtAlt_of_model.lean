-- Prove2me | Theorems.Thm_Formalism_ELL_unitAtAlt_of_model
-- name    : Formalism.ELL.unitAtAlt.of_model
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:53.182479+00:00
-- url     : https://prove2.me/theorems/d88f9e8b-fd2e-4b68-82b7-b6fcbdc4e1ff
-- title:
--   unit At Alt: of model
-- statement:
--   The unit At Alt construction uses the of model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ModelUnitOf.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ModelUnitOf.lean#L28-L37

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ModelUnitOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism Formalism.ELL Formalism.ELL.unitAtAlt
open Formalism.ELL

theorem Formalism.ELL.unitAtAlt.of_model {K : Type u} [NormedField K] (W : WeierstrassCurve K) (j : K)
    (hI : IntegralModel W) (hc : W.c₄ ^ 3 = j * W.Δ) (hΔ : ‖W.Δ‖ = 1) :
    ∃ (W : WeierstrassCurve K) (_ : W.IsElliptic),
      IntegralModel W ∧ ‖W.Δ‖ = 1 ∧ W.j = j := by sorry
