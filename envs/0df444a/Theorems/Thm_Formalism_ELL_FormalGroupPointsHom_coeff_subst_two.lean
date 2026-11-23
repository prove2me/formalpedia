-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_coeff_subst_two
-- name    : Formalism.ELL.FormalGroupPointsHom.coeff_subst_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:26:38.606377+00:00
-- url     : https://prove2.me/theorems/8dcbf1be-e27e-4ce7-b205-34bb6f9172a0
-- title:
--   Formal Group Points Hom: coeff subst two
-- statement:
--   The Formal Group Points Hom construction uses the coeff subst two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L189-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L189-L198

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
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
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsHom
open Formalism.ELL Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem Formalism.ELL.FormalGroupPointsHom.coeff_subst_two (G s t : MvPowerSeries (Fin 2) K) (hs0 : MvPowerSeries.constantCoeff s = 0)
    (ht0 : MvPowerSeries.constantCoeff t = 0) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (G.subst ![s, t]) =
      ∑ᶠ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d G * MvPowerSeries.coeff e (s ^ (d 0) * t ^ (d 1)) := by sorry
