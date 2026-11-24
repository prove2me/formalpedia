-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rowsOK_prodAll
-- name    : Formalism.L2.FormalSeriesBounds.rowsOK_prodAll
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:51:19.361953+00:00
-- url     : https://prove2.me/theorems/400095eb-995d-467a-87ad-9c3a3b18ace8
-- title:
--   Formal Series Bounds: rows OK prod All
-- statement:
--   The Formal Series Bounds construction uses the rows OK prod All property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/MemVarsProdAll.lean#L88-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/MemVarsProdAll.lean#L88-L119

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

theorem Formalism.L2.FormalSeriesBounds.rowsOK_prodAll (G : ∀ g, Cart V d (I g) (J g)) (alt : Prop)
    {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} (hpl : Function.Injective pl)
    (P : ∀ i, MvPolynomial (Fin (what₂ i) × WV I) C) (kind : ∀ i, Fin (what₂ i) → Knd d)
    (h : ∀ i, RowsOK G alt (P i) (kind i)) : RowsOK G alt (prodAll pl P) (kindAll pl kind) := by sorry
