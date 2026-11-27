-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_mem_tySet_iff
-- name    : Formalism.L2.FormalSeriesBounds.RawChart.mem_tySet_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T05:20:30.681497+00:00
-- url     : https://prove2.me/theorems/acc06b48-07a3-43a1-bf58-bba8cc16da9f
-- title:
--   Raw Chart: mem ty Set iff
-- statement:
--   The Raw Chart construction uses the mem ty Set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L74-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L74-L75

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

theorem Formalism.L2.FormalSeriesBounds.RawChart.mem_tySet_iff (X : RawChart C d I κ) (V : VF C) (g : Fin 2) (x : ℕ → I g ⊕ JJ I g → C) :
    x ∈ X.TySet V g ↔ ∃ γ lam, X.TyWit V g x γ lam := by sorry
