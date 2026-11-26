-- Prove2me | Theorems.Thm_Eden_sum_antitone_embedding_le
-- name    : Eden.sum_antitone_embedding_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:01:30.94858+00:00
-- url     : https://prove2.me/theorems/68437a27-f36e-4477-8813-1a83c33ed5bc
-- title:
--   Eden: sum antitone embedding le
-- statement:
--   The Eden construction uses the sum antitone embedding le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SelectedSums.lean#L38-L53
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SelectedSums.lean#L38-L53

import Definitions.Def_Eden_Sorting
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Hom.PowersetCard
import Definitions.Def_Eden_SelectedSums
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.sum_antitone_embedding_le {k n : ℕ} (hk : k ≤ n) {a : Fin n → ℝ}
    (ha : Antitone a) (e : Fin k ↪ Fin n) :
    (∑ i : Fin k, a (e i)) ≤ ∑ i : Fin k, a (Fin.castLE hk i) := by sorry
