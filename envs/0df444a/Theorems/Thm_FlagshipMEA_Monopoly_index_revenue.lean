-- Prove2me | Theorems.Thm_FlagshipMEA_Monopoly_index_revenue
-- name    : FlagshipMEA.Monopoly.index_revenue
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:08:38.301982+00:00
-- url     : https://prove2.me/theorems/409e8c0f-bc09-42ef-9684-2a21bae4ed39
-- title:
--   §2.1 — MEA index equals concentrated-strategy revenue
-- statement:
--   For a product $i$ and positive total marketing effort $M$, allocate all $M$ to product $i$ and zero to every other product. The MEA index of Definition 2 equals the firm's revenue under this allocation:
--
--   $$R_i(M)=\operatorname{rev}(M e_i).$$
--
--   This gives the index its economic meaning and connects the index comparison to the firm's fixed-effort revenue problem. **Formalization Note** The index is used only when $M>0$, its domain in Definition 2.
-- source:
--   He, Ke & Zhang, A Model of Product Line Marketing, SSRN 3631879 (version of August 2021), p. 12 (PDF 14), text immediately after Definition 2

import Mathlib
import Definitions.Def_FlagshipMEA_Monopoly_Model

namespace FlagshipMEA.Monopoly

/-- The sentence following Definition 2 (p. 12): the index is the revenue of a
strategy assigning the entire positive TME to its indexed product. -/
theorem index_revenue {n : ℕ} (D : Data n) (hS : D.Standing)
    (i : Fin n) (M : ℝ) (hM : 0 < M) :
    D.R i M = D.revenue (fun j => if j = i then M else 0) := by sorry

end FlagshipMEA.Monopoly
