-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassSubstitution_mvsubst_psubst
-- name    : Formalism.ELL.WeierstrassSubstitution.mvsubst_psubst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:59.988824+00:00
-- url     : https://prove2.me/theorems/7081937b-03e6-4f46-be31-f85a0c96482e
-- title:
--   Weierstrass Substitution: mvsubst psubst
-- statement:
--   The Weierstrass Substitution construction uses the mvsubst psubst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WSubst.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WSubst.lean#L11-L18

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
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
open Formalism Formalism.ELL Formalism.ELL.WeierstrassSubstitution

theorem Formalism.ELL.WeierstrassSubstitution.mvsubst_psubst {K : Type u} [Field K] {τ σ : Type} (w : PowerSeries K)
    (a : MvPowerSeries τ K) (ha : MvPowerSeries.constantCoeff a = 0)
    (b : τ → MvPowerSeries σ K) (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (w.subst a) = w.subst (MvPowerSeries.subst b a) := by sorry
