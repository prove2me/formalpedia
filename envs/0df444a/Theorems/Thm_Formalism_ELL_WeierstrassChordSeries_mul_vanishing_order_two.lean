-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_mul_vanishing_order_two
-- name    : Formalism.ELL.WeierstrassChordSeries.mul_vanishing_order_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:19:36.887219+00:00
-- url     : https://prove2.me/theorems/ad7038b2-d033-4dff-ab5e-2f58900a7478
-- title:
--   Weierstrass Chord Series: mul vanishing order two
-- statement:
--   The Weierstrass Chord Series construction uses the mul vanishing order two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L437-L439
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L437-L439

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
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
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff

theorem Formalism.ELL.WeierstrassChordSeries.mul_vanishing_order_two {φ : MvPowerSeries (Fin 2) K} (h0 : cc φ = 0) (h1 : ∀ i, (L i) φ = 0)
    (ψ : MvPowerSeries (Fin 2) K) : cc (φ * ψ) = 0 ∧ ∀ i, (L i) (φ * ψ) = 0 := by sorry
