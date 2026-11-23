-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_hasSubst2
-- name    : Formalism.ELL.FormalGroupPointsHom.hasSubst2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:26:09.80632+00:00
-- url     : https://prove2.me/theorems/3cc77548-5145-4087-9dda-a3f6d297d4f7
-- title:
--   Formal Group Points Hom: has Subst2
-- statement:
--   The Formal Group Points Hom construction uses the has Subst2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L529-L531
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L529-L531

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

theorem Formalism.ELL.FormalGroupPointsHom.hasSubst2 {s t : MvPowerSeries (Fin 2) K} (hs : MvPowerSeries.constantCoeff s = 0)
    (ht : MvPowerSeries.constantCoeff t = 0) : MvPowerSeries.HasSubst ![s, t] := by sorry
