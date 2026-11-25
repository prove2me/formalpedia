-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_shift_add
-- name    : Formalism.L2.FormalSeriesBounds.RF.shift_add
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:02:10.058274+00:00
-- url     : https://prove2.me/theorems/b86d4946-5048-4ac1-8e39-ed2d8e4a9a4e
-- title:
--   RF: shift add
-- statement:
--   The RF construction uses the shift add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemCInv.lean#L34-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemCInv.lean#L34-L48

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCInv
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
variable {T : Type} {r : T → ℕ} {n : ℕ} {C : Type} [Field C]
variable {N N' : ℕ} (Φ : MvPolynomial (Fin N × Fin N') C →ₐ[C] MvPolynomial (Letter T r n) C) (σ0 : T)
  (w : Fin N → Fin 2 → C) (lt : Fin N × Fin N' → Fin 2 → Letter T r n) (colf : Fin N → Fin 2 → Fin n)

theorem Formalism.L2.FormalSeriesBounds.RF.shift_add (hΦ : ∀ x, Φ (X x) = ∑ q, MvPolynomial.C (w x.1 q) * X (lt x q))
    (hlt : ∀ ρ c q, keyL (lt (ρ, c) q) = (σ0, c.val, colf ρ q)) (i i' : Fin (r σ0)) (t : C)
    (ρ : Fin N) (c c' : Fin N') (hc : c.val = i.val) (hc' : c'.val = i'.val) :
    rowShift r n C σ0 i i' t (Φ (X (ρ, c))) = Φ (X (ρ, c)) + MvPolynomial.C t * Φ (X (ρ, c')) := by sorry
