-- Prove2me | Theorems.Thm_Eden_prod_antitone_embedding_le
-- name    : Eden.prod_antitone_embedding_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:08:29.557318+00:00
-- url     : https://prove2.me/theorems/207aabfe-7914-514a-84d3-402eea05dabc
-- title:
--   Eden: prod antitone embedding le
-- statement:
--   The Eden construction uses the prod antitone embedding le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SelectedProducts.lean#L14-L30
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SelectedProducts.lean#L14-L30

import Definitions.Def_Eden_SelectedSums
import Definitions.Def_Eden_SelectedProducts
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.prod_antitone_embedding_le {k n : ℕ} (hk : k ≤ n) {a : Fin n → ℝ}
    (ha : Antitone a) (hpos : ∀ i, 0 ≤ a i) (e : Fin k ↪ Fin n) :
    (∏ i : Fin k, a (e i)) ≤ ∏ i : Fin k, a (Fin.castLE hk i) := by sorry
