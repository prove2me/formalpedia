-- Prove2me | Theorems.Thm_EdenVerified_s04_exteriorOperator_comp
-- name    : EdenVerified.s04_exteriorOperator_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:52:10.441867+00:00
-- url     : https://prove2.me/theorems/021fa84a-581f-40cb-981f-a804da5317b9
-- title:
--   Eden Verified: s04 exterior Operator comp
-- statement:
--   The Eden Verified construction uses the s04 exterior Operator comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1827-L1830
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1827-L1830

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s04_exteriorOperator_comp :
    ∀ (k : ℕ) (A B : PhaseSpace →ₗ[ℝ] PhaseSpace),
    exteriorOperator k (A ∘ₗ B) = (exteriorOperator k A).comp (exteriorOperator k B) := by sorry
