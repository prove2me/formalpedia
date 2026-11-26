-- Prove2me | Theorems.Thm_EdenVerified_s04_singularValueFunction_integer_comp_le
-- name    : EdenVerified.s04_singularValueFunction_integer_comp_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:52:11.920717+00:00
-- url     : https://prove2.me/theorems/e1340397-cfd2-5e75-ac71-5daa74db28bb
-- title:
--   Eden Verified: s04 singular Value Function integer comp le
-- statement:
--   The Eden Verified construction uses the s04 singular Value Function integer comp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1832-L1836
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1832-L1836

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s04_singularValueFunction_integer_comp_le :
    ∀ {k : ℕ} (hk : k ≤ 5)
    (A B : PhaseSpace →ₗ[ℝ] PhaseSpace),
    singularValueFunction (A ∘ₗ B) k ≤ singularValueFunction A k * singularValueFunction B k := by sorry
