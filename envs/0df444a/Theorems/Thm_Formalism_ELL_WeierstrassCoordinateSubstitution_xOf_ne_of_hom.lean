-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_xOf_ne_of_hom
-- name    : Formalism.ELL.WeierstrassCoordinateSubstitution.xOf_ne_of_hom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:28.157154+00:00
-- url     : https://prove2.me/theorems/7d2ea659-c754-4769-a2fe-c36e88000d8f
-- title:
--   Weierstrass Coordinate Substitution: x Of ne of hom
-- statement:
--   The Weierstrass Coordinate Substitution construction uses the x Of ne of hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExistsUnitFactor.lean#L67-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExistsUnitFactor.lean#L67-L80

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
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
open Formalism.ELL.WeierstrassCoordinateSubstitution
variable {K : Type u} [Field K]

theorem Formalism.ELL.WeierstrassCoordinateSubstitution.xOf_ne_of_hom {u w : PowerSeries K} (hwu : w = X ^ 3 * u) (hu : constantCoeff u = 1)
    {σ : Type} (φ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K) (s t : MvPowerSeries σ K)
    (hs0 : MvPowerSeries.constantCoeff s = 0) (ht0 : MvPowerSeries.constantCoeff t = 0)
    (hs : s ≠ 0) (ht : t ≠ 0) (hφs : φ s = 0) (hφt : φ t ≠ 0) : xOf w s ≠ xOf w t := by sorry
