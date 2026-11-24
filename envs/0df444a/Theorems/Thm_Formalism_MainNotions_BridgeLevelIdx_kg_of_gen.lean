-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLevelIdx_kg_of_gen
-- name    : Formalism.MainNotions.BridgeLevelIdx.kg_of_gen
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:42:34.404802+00:00
-- url     : https://prove2.me/theorems/067ab8e0-8cf5-4fe0-84f3-d16f10f22f65
-- title:
--   Bridge Level Idx: kg of gen
-- statement:
--   The Bridge Level Idx construction uses the kg of gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelIdx.lean#L42-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelIdx.lean#L42-L76

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelIdx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelIdx
open MeasureTheory Formalism.MainNotions.S Matrix
open scoped ENNReal TensorProduct
variable (I : AutInst)
variable {I}

theorem Formalism.MainNotions.BridgeLevelIdx.kg_of_gen {g : ℕ} {m : ℕ} {l : Fin m → (Fin I.n → I.E ⊗[I.F] Af I.F)}
    (hgen : ∀ y ∈ I.Lf, ∃ (a : Fin m → IntAf I.F I.E) (z : Fin I.n → I.E ⊗[I.F] Af I.F), z ∈ I.Lf ∧
      y = ∑ j, (a j : I.E ⊗[I.F] Af I.F) • l j + (g : I.E ⊗[I.F] Af I.F) • z)
    {x x' : I.Gf} (hx : x ∈ I.Kset) (hx' : x' ∈ I.Kset)
    (hd : ∀ j, ∃ w ∈ I.Lf, (I.fmat x' - I.fmat x) *ᵥ l j = (g : I.E ⊗[I.F] Af I.F) • w) :
    x⁻¹ * x' ∈ I.Kg g := by sorry
