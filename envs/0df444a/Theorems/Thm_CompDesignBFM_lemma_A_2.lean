-- Prove2me | Theorems.Thm_CompDesignBFM_lemma_A_2
-- name    : CompDesignBFM.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:33:21.407045+00:00
-- url     : https://prove2.me/theorems/efc99fa0-3a17-4fbd-b505-8e755a3ab8ee
-- title:
--   Lemma A.2 — benchmark preservation
-- statement:
--   Let $v$ be normalized and nonnegative and $B>0$. For every nonnegative cost vector $c$,
--
--   $$\mathrm{OPT}_{\hat v}(c)=\mathrm{OPT}_v(c).$$
--
--   Differences from the source: none.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Lemma A.2, p.40 (PDF 42)

import Mathlib
import Definitions.Def_CompDesignBFM_closure
import Definitions.Def_CompDesignBFM_OPT

namespace CompDesignBFM

/-- Lemma A.2, Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.40, PDF 42. For every nonnegative cost vector `c`, `OPT_v̂(c) = OPT_v(c)`, for a normalized
nonnegative `v` (Appendix A, p.40) and a budget `B > 0`. -/
theorem lemma_A_2 {n : ℕ} (v : Finset (Fin n) → ℝ) (hv0 : v ∅ = 0) (hv : ∀ S, 0 ≤ v S) (B : ℝ) (hB : 0 < B)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) :
    OPT (closure v) B c = OPT v B c := by sorry

end CompDesignBFM
