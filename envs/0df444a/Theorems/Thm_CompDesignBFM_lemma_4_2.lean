-- Prove2me | Theorems.Thm_CompDesignBFM_lemma_4_2
-- name    : CompDesignBFM.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:36:17.795255+00:00
-- url     : https://prove2.me/theorems/4912a0c6-9655-4c8d-b6bc-1077e8b74acc
-- title:
--   Lemma 4.2 — the singleton branch is truthful, IR, budget feasible, with value M
-- statement:
--   For a budget $B>0$ and a fixed agent priority, the singleton branch is truthful, individually rational and budget feasible, and it pays nonnegative amounts only to selected agents. If $v(\emptyset)=0$, then under truthful bidding $c\ge0$ its value is $M=\max\{v(\{i\}):c_i\le B\}$.
--
--   Differences from the source:
--   - encoding: ties among agents are resolved by a fixed priority order (Remark 2.1) → an injective rank rho on agents; reason: a finite total order is such a rank
--   - encoding: M = max{v({i}) : c_i ≤ B} → M is 0 when no agent is affordable; reason: the value of the singleton branch there; the source's maximum is otherwise unchanged
--   - generalization: v is a normalized nonnegative value function → the mechanism properties hold for every real-valued v; reason: the allocation only compares singleton values; normalized nonnegative v are instances
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Lemma 4.2, p.21 (PDF 23)

import Mathlib
import Definitions.Def_CompDesignBFM_singletonMech
import Definitions.Def_CompDesignBFM_IsGood
import Definitions.Def_CompDesignBFM_M

namespace CompDesignBFM

/-- Lemma 4.2, Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.21, PDF 23. The singleton branch is truthful, individually rational and budget
feasible. Under truthful bidding, its value is `M`. -/
theorem lemma_4_2 {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (hB : 0 < B) (rho : Fin n → ℕ)
    (hrho : Function.Injective rho) :
    IsGood B (singletonMech v B rho) ∧
      (v ∅ = 0 → ∀ c : Fin n → ℝ, (∀ i, 0 ≤ c i) → v ((singletonMech v B rho).alloc c) = M v B c) := by sorry

end CompDesignBFM
