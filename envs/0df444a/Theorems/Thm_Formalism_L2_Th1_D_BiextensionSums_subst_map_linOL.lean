-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_BiextensionSums_subst_map_linOL
-- name    : Formalism.L2.Th1.D.BiextensionSums.subst_map_linOL
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:04:49.467498+00:00
-- url     : https://prove2.me/theorems/13c45d9e-466c-4230-941f-8a5f4e22b387
-- title:
--   Biextension Sums: subst map lin OL
-- statement:
--   The Biextension Sums construction uses the subst map lin OL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionOfExpSpec.lean#L64-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionOfExpSpec.lean#L64-L75

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionPointsOfExpSpec
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionOfExpSpec
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_mvExp_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog thetaZ bSum linSub idM ZV)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog mvExp_add)
open MvPowerSeries
open Pair
open Formalism.L2.Th1.D.BiextensionSums

theorem Formalism.L2.Th1.D.BiextensionSums.subst_map_linOL {K0 K : Type} [NormedField K0] [NormedField K] {d N0 N1 : ℕ} [NeZero d]
    (l : ℕ) (j : K0 →+* K) (σ : K0 →+* K0) (c : K0) (a : Fin N0) (b : Fin N1)
    {g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K} (hg : HasSubst g)
    (hgE : ∀ y, subst g (entLog (K := K) l y) = X y) :
    subst g (map j (linOL σ c (fun s : ZMod d => entLog (K := K0) l (s, a, b)))) =
      ∑ s : ZMod d, if s.val % 2 = 0 then 0 else C (j (σ^[s.val] c)) * X (s, a, b) := by sorry
