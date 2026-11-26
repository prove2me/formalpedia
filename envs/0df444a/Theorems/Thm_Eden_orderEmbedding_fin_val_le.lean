-- Prove2me | Theorems.Thm_Eden_orderEmbedding_fin_val_le
-- name    : Eden.orderEmbedding_fin_val_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:01:25.68103+00:00
-- url     : https://prove2.me/theorems/b645977c-be06-4fd0-9dda-f6e49eed4f60
-- title:
--   Eden: order Embedding fin val le
-- statement:
--   The Eden construction uses the order Embedding fin val le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SelectedSums.lean#L27-L36
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SelectedSums.lean#L27-L36

import Definitions.Def_Eden_Sorting
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Hom.PowersetCard
import Definitions.Def_Eden_SelectedSums
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.orderEmbedding_fin_val_le {k n : ℕ} (e : Fin k ↪o Fin n) (i : Fin k) :
    i.val ≤ (e i).val := by sorry
