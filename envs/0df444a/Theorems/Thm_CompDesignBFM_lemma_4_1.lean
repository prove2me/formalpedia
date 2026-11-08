-- Prove2me | Theorems.Thm_CompDesignBFM_lemma_4_1
-- name    : CompDesignBFM.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:36:36.55419+00:00
-- url     : https://prove2.me/theorems/a5bc67e9-5d8a-41dc-8919-970092ecd18f
-- title:
--   Lemma 4.1 — A_mc is nonbossy and (A_mc, τ) is truthful, IR and budget feasible
-- statement:
--   For any self-bounding proxy $F$, budget $B>0$ and fixed priority with $\emptyset$ first, the allocation rule $A_{\mathrm{mc}}$ is nonbossy. Equipped with the threshold payments $\tau$, the mechanism $(A_{\mathrm{mc}},\tau)$ is truthful, individually rational and budget feasible, pays nonnegative amounts only to selected agents, and its thresholds are finite.
--
--   Differences from the source:
--   - encoding: a fixed priority order on sets with ∅ first (Remark 2.1) → an injective rank r with r ∅ least; reason: a finite total order is such a rank
--   - generalization: the proxy is normalized (p.6: 'a normalized monotone proxy F') → F ∅ = 0 is not assumed; reason: the lemma as printed reads 'any self-bounding proxy F', and the ∅-first tie-breaking is all the argument needs; the normalized case is an instance
--   - generalization: §4.1 (p.20) 'we are given a subadditive and self-bounding proxy F' → subadditivity of F is not assumed; reason: the lemma as printed reads 'any self-bounding proxy F', and neither nonbossiness nor the threshold bound uses subadditivity; subadditive proxies are instances
--   - generalization: conclusion: nonbossy, truthful, IR, budget feasible → also: payments nonnegative and zero off the allocation, and the threshold sets bounded above; reason: the extra clauses make the real supremum in τ a true one and imply the printed conclusion
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Lemma 4.1, p.21 (PDF 23)

import Mathlib
import Definitions.Def_CompDesignBFM_IsSelfBounding
import Definitions.Def_CompDesignBFM_IsPriority
import Definitions.Def_CompDesignBFM_Amc
import Definitions.Def_CompDesignBFM_IsNonbossy
import Definitions.Def_CompDesignBFM_thresholdMech
import Definitions.Def_CompDesignBFM_IsGood

namespace CompDesignBFM

/-- Lemma 4.1, Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.21, PDF 23. For any self-bounding proxy `F`, the allocation rule `A_mc` is nonbossy,
and with the threshold payments `τ` the mechanism `(A_mc, τ)` is truthful, individually rational and budget
feasible.
**Formalization Note.** The third clause records that the thresholds of `A_mc` are finite (the proof bounds
them by `B`), so the real `sSup` in `tau` is a true supremum. -/
theorem lemma_4_1 {n : ℕ} (F : Finset (Fin n) → ℝ) (B : ℝ) (hB : 0 < B) (hF : IsSelfBounding F)
    (r : Finset (Fin n) → ℕ) (hr : IsPriority r) :
    IsNonbossy (Amc F B r) ∧ IsGood B (thresholdMech (Amc F B r)) ∧
      ∀ b : Fin n → ℝ, (∀ j, 0 ≤ b j) → ∀ i,
        BddAbove {z : ℝ | 0 ≤ z ∧ i ∈ Amc F B r (Function.update b i z)} := by sorry

end CompDesignBFM
