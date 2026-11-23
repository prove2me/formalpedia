-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_inv_formal
-- name    : Formalism.ELL.FormalGroupPointsHom.inv_formal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:28.322421+00:00
-- url     : https://prove2.me/theorems/85dc1aed-7a42-4fea-a34a-8e2697f899ea
-- title:
--   Formal Group Points Hom: inv formal
-- statement:
--   The Formal Group Points Hom construction uses the inv formal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L586-L697
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L586-L697

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
variable {K : Type u} [Field K]

theorem Formalism.ELL.FormalGroupPointsHom.inv_formal (hU : WSubstUnique.{u}) (hS : WChordSubst.{u}) {W : WeierstrassCurve K}
    {w : PowerSeries K} (hw : WFixed W w) (F : FormalGroup K)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F.toPowerSeries)
    (ψ : MvPowerSeries (Fin 2) K)
    (hψ : (1 - MvPowerSeries.C W.a₁ * MvPowerSeries.X 0 - MvPowerSeries.C W.a₃ *
      w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) * ψ = 1) :
    F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      -MvPowerSeries.X 0 * ψ] = 0 := by sorry
