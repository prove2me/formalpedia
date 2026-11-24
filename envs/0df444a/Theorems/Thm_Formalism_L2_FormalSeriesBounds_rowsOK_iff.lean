-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rowsOK_iff
-- name    : Formalism.L2.FormalSeriesBounds.rowsOK_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:05.103494+00:00
-- url     : https://prove2.me/theorems/bbbc6338-3f42-4e00-baea-30e4762b08ba
-- title:
--   Formal Series Bounds: rows OK iff
-- statement:
--   The Formal Series Bounds construction uses the rows OK iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/MemVarsProdAll.lean#L68-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/MemVarsProdAll.lean#L68-L86

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
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
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  {N K : ℕ} {what₂ : Fin K → ℕ}

theorem Formalism.L2.FormalSeriesBounds.rowsOK_iff (G : ∀ g, Cart V d (I g) (J g)) (alt : Prop) {N : ℕ} (P : MvPolynomial (Fin N × WV I) C)
    (kind : Fin N → Knd d) : RowsOK G alt P kind ↔
      (∀ ρ g a a', kind ρ = some (g, a, a') → alt ∧ Odd (a' - a).val ∧
        ∀ w, (ρ, w) ∈ P.vars → OnLeafV G g a a' w) ∧
      (∀ ρ, kind ρ = none → ∃ g : Fin 2, ∀ w : WV I, (ρ, w) ∈ P.vars → w.1 = g) := by sorry
