-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_hLf_leaf
-- name    : Formalism.L2.FormalSeriesBounds.RawChart.hLf_leaf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:57.704483+00:00
-- url     : https://prove2.me/theorems/72312ea2-8266-4fcc-a6c5-fc59a04b26a6
-- title:
--   Raw Chart: h Lf leaf
-- statement:
--   The Raw Chart construction uses the h Lf leaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieDefs.lean#L130-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieDefs.lean#L130-L135

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IntSubst
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDefs
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
variable {X}
variable (X)

theorem Formalism.L2.FormalSeriesBounds.RawChart.hLf_leaf (g : Fin 2) (a a' : ZMod d) (μ : WV I →₀ ℕ)
    (h : MvPowerSeries.coeff μ (X.hLf g a a') ≠ 0) : ∀ w ∈ μ.support, X.OnLf g a a' w := by sorry
