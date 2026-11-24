-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_IsogenyPAux_ext_at
-- name    : Formalism.L2.Th1.F.IsogenyPAux.ext_at
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:33.278844+00:00
-- url     : https://prove2.me/theorems/9523fa11-a20b-4814-a971-0f10c28fdd09
-- title:
--   Isogeny PAux: ext at
-- statement:
--   The Isogeny PAux construction uses the ext at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenyP.lean#L38-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenyP.lean#L38-L68

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Elliptic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenyP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.IsogenyPAux

theorem Formalism.L2.Th1.F.IsogenyPAux.ext_at (L : PeriodPair) (α : ℂ) (T : Finset ℂ) (hα : α ≠ 0) (hst : MulStable L α)
    (h1 : ∀ P ∈ T, α * P ∈ L.lattice)
    (h2 : ∀ P ∈ T, ∀ Q ∈ T, P - Q ∈ L.lattice → P = Q)
    (z₀ P' : ℂ) (hP' : P' ∈ T) (hz : z₀ + P' ∈ L.lattice) :
    AnalyticAt ℂ (fun w => α ^ 2 * L.weierstrassPExcept 0 (α * (w - z₀))
        - L.weierstrassPExcept 0 (1 * (w - z₀)) - ∑ P ∈ T.erase P', L.weierstrassP (1 * w + P)) z₀ ∧
    (fun w => α ^ 2 * L.weierstrassP (α * w) - ∑ P ∈ T, L.weierstrassP (w + P)) =ᶠ[𝓝[≠] z₀]
      (fun w => α ^ 2 * L.weierstrassPExcept 0 (α * (w - z₀))
        - L.weierstrassPExcept 0 (1 * (w - z₀)) - ∑ P ∈ T.erase P', L.weierstrassP (1 * w + P)) := by sorry
