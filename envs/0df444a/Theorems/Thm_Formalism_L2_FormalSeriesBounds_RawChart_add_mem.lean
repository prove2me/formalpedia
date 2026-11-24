-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_add_mem
-- name    : Formalism.L2.FormalSeriesBounds.RawChart.add_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:39:27.161581+00:00
-- url     : https://prove2.me/theorems/b50d7f92-ea94-400f-9958-1e243a6143ef
-- title:
--   Raw Chart: add mem
-- statement:
--   The Raw Chart construction uses the add mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NegMem.lean#L37-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NegMem.lean#L37-L72

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValNonnegLeadingCoeffOfMemTySet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem Formalism.L2.FormalSeriesBounds.RawChart.add_mem (V : VF C) (g : Fin 2) (hA : X.AddCvSt V) (hu : ∀ g c i, V.Ge 0 (X.u g c i))
    (x y : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) (hy : y ∈ X.TySet V g) : x + y ∈ X.TySet V g := by sorry
