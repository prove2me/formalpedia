-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_E2_parallelogram_three_weierstrass_key
-- name    : Formalism.L2.Th1.B.E2.parallelogram_three_weierstrass_key
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:02:14.533808+00:00
-- url     : https://prove2.me/theorems/7e46b324-0a0b-49c9-9c1e-e810692d7fab
-- title:
--   E2: parallelogram three weierstrass key
-- statement:
--   The E2 construction uses the parallelogram three weierstrass key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/ConstantCoeffLawWithInverseThree.lean#L341-L450
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/ConstantCoeffLawWithInverseThree.lean#L341-L450

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffLawWithInverseThree
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_G_LogP_subst_XX
import Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.E2
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob in3)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst subst_XX subst_zero')
variable {K : Type} [NormedField K] [CharZero K]

theorem Formalism.L2.Th1.B.E2.parallelogram_three_weierstrass_key (hA : FrobStickStar) {g2 g3 s2 c0 a1 a3 : K} {P l i ep : PowerSeries K}
    {F n : MvPowerSeries (Fin 2) K} {e : MvPowerSeries (Fin 3) K} (hP : IsWp g2 g3 P)
    (hF : LawLog F l) (hi : IsInv l i)
    (h2 : PowerSeries.X ^ 2 * (1 + l ^ 2 * PowerSeries.subst l P) =
      l ^ 2 * (ep + PowerSeries.C c0 * PowerSeries.X ^ 2))
    (h3 : PowerSeries.X ^ 3 * (-2 + l ^ 3 * PowerSeries.subst l (PowerSeries.derivative K P)) =
      l ^ 3 * (-2 * ep + PowerSeries.C a1 * PowerSeries.X * ep +
        PowerSeries.C a3 * PowerSeries.X ^ 3))
    (he : Matrix.det (Matrix.of fun j : Fin 3 =>
        ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K) ^ 3, MvPowerSeries.X j * at1 j ep,
          -at1 j ep]) =
        e * F3 F * (MvPowerSeries.X 0 - MvPowerSeries.X 1) *
          (MvPowerSeries.X 0 - MvPowerSeries.X 2) * (MvPowerSeries.X 1 - MvPowerSeries.X 2))
    (hn : FI F i = (MvPowerSeries.X 0 - MvPowerSeries.X 1) * n) :
    MvPowerSeries.constantCoeff (par3 F i (phO s2 P l)) = 0 ∧
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] n *
      MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n *
      MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n *
      fExp (-par3 F i (phO s2 P l)) = -e := by sorry
