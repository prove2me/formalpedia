-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_ISer_eq_wSer_subst
-- name    : Formalism.L2.Th1.A.ISer.eq_wSer_subst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:28.245529+00:00
-- url     : https://prove2.me/theorems/2ffee3b6-44d3-4545-8f46-84d34f38ce4d
-- title:
--   ISer: eq w Ser subst
-- statement:
--   The ISer construction uses the eq w Ser subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/EqWSerSubst.lean#L30-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/EqWSerSubst.lean#L30-L60

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.ISer
variable {R : Type u} [CommRing R]

theorem Formalism.L2.Th1.A.ISer.eq_wSer_subst (hW : WSerSpec.{u}) (W : WeierstrassCurve R) (s v : R⟦X⟧)
    (hs : constantCoeff s = 0) (hv : constantCoeff v = 0)
    (h : v = s ^ 3 + C W.a₁ * s * v + C W.a₂ * s ^ 2 * v + C W.a₃ * v ^ 2 + C W.a₄ * s * v ^ 2
      + C W.a₆ * v ^ 3) : v = (wSer W).subst s := by sorry
