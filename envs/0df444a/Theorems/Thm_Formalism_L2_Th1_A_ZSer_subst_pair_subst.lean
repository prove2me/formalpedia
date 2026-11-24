-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_ZSer_subst_pair_subst
-- name    : Formalism.L2.Th1.A.ZSer.subst_pair_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:11.729666+00:00
-- url     : https://prove2.me/theorems/d83ed13c-6134-4b5d-835b-b7257cca4845
-- title:
--   ZSer: subst pair subst
-- statement:
--   The ZSer construction uses the subst pair subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/SubstPairSubst.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/SubstPairSubst.lean#L33-L39

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_SubstPairSubst
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.ZSer
local notation "FF[" W "](" a ", " b ")" =>
  MvPowerSeries.subst (![a, b] : Fin 2 → PowerSeries _) (fgl W)
variable {R : Type u} [CommRing R]

theorem Formalism.L2.Th1.A.ZSer.subst_pair_subst {a b : R⟦X⟧} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    {g : MvPowerSeries (Fin 2) R} (hg : MvPowerSeries.constantCoeff g = 0) (f : R⟦X⟧) :
    MvPowerSeries.subst (![a, b] : Fin 2 → R⟦X⟧) (f.subst g)
      = f.subst (MvPowerSeries.subst (![a, b] : Fin 2 → R⟦X⟧) g) := by sorry
