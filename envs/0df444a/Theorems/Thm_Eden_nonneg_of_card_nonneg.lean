-- Prove2me | Theorems.Thm_Eden_nonneg_of_card_nonneg
-- name    : Eden.nonneg_of_card_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:57:19.088882+00:00
-- url     : https://prove2.me/theorems/11c21dc7-664d-5ff1-8c0e-6e000b3bda94
-- title:
--   Eden: nonneg of card nonneg
-- statement:
--   The Eden construction uses the nonneg of card nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NeutralDimensionBounds.lean#L16-L31
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NeutralDimensionBounds.lean#L16-L31

import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_NeutralDimensionBounds
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.nonneg_of_card_nonneg {n : ℕ} {a f : Fin n → ℝ} (ha : Antitone a)
    (hm : Finset.univ.val.map a = Finset.univ.val.map f) (i : Fin n)
    (hi : i.val < (Finset.univ.filter (fun j => 0 ≤ f j)).card) : 0 ≤ a i := by sorry
