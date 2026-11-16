-- Prove2me | Theorems.Thm_CompDesignBFM_Supplement_theorem_C_4
-- name    : CompDesignBFM.Supplement.theorem_C_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:09:59.973241+00:00
-- url     : https://prove2.me/theorems/1a600406-6fee-417a-8c45-a1748948a871
-- title:
--   Theorem C.4 — on the 2-PH valuation (39) every universally truthful budget-feasible mechanism has expected value $0$ at some $c_x$ with $\mathrm{OPT}(c_x)=1$
-- statement:
--   Let $B>0$ and let $v$ be the valuation (39) on two agents: $v(\emptyset)=v(\{1\})=v(\{2\})=0$, $v(\{1,2\})=1$. Let $R$ be a randomized mechanism, a probability distribution over deterministic mechanisms each of which is truthful, individually rational, pays nonnegative amounts only to selected agents, and is budget feasible. Then there is $x\in(0,B)$ such that, at the cost vector $c_x=(x,B-x)$,
--
--   $$\mathbb E\bigl[v(S_R(c_x))\bigr]=0\qquad\text{while}\qquad\mathrm{OPT}(c_x)=1,$$
--
--   where $S_R(c_x)$ is the set selected under truthful bidding. Hence no universally truthful mechanism has bounded approximation for $\beta$-MPH valuations with $\beta\ge2$ without a large-market assumption.
--
--   Differences from the source:
--   - encoding: a randomized (universally truthful) mechanism, a distribution over deterministic mechanisms → a probability space (Ω, P) with a map R into deterministic mechanisms, each IsGood B, whose allocation events {ω | alloc_ω(b) = S} are measurable at nonnegative bids; reason: the expected value at each bid vector needs these events measurable; any distribution over mechanisms is the law of such a map
--   - encoding: expected value E[v(S)] → Σ_S P(alloc_ω(c_x) = S)·v(S); reason: the allocation takes finitely many values, so this is the expectation
--   - encoding: individually rational, budget feasible → IsGood B, which also includes nonnegative payments and zero payments to unselected agents; reason: the model of p.1; Lemma C.4 of the proof uses that unselected agents are paid zero
--   - encoding: agents 1, 2 → 0, 1 : Fin 2; reason: indexing
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Theorem C.4, p.49 (PDF 51); valuation (39) and c_x, p.48 (PDF 50)

import Mathlib
import Definitions.Def_CompDesignBFM_Mechanism
import Definitions.Def_CompDesignBFM_IsGood
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesignBFM_Supplement_pairValue

namespace CompDesignBFM

namespace Supplement

/-- Theorem C.4 (impossibility for randomized mechanisms), Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.49, PDF 51. For the 2-PH valuation
(39) and any budget `B > 0`, every universally truthful, individually rational, budget-feasible
mechanism admits a cost vector `c_x = (x, B − x)`, `x ∈ (0, B)`, at which its expected value is zero
while `OPT(c_x) = 1`.
**Formalization Note.** A randomized mechanism is an arbitrary probability space `(Ω, P)` with a
realization map `R` into deterministic mechanisms; "universally" means every realization is `IsGood B`
(truthful, IR, nonnegative payments to selected agents only, budget feasible). The events
`{ω | (R ω).alloc b = S}` are assumed measurable at nonnegative bids, so that the expected value
`∑_S P(alloc(c_x) = S) · v(S)` is defined; bids are truthful (`b = c_x`). -/
theorem theorem_C_4 (B : ℝ) (hB : 0 < B) (Ω : Type*) [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (R : Ω → Mechanism 2) (hR : ∀ ω, IsGood B (R ω))
    (hmeas : ∀ b : Fin 2 → ℝ, (∀ j, 0 ≤ b j) → ∀ S : Finset (Fin 2),
      MeasurableSet {ω | (R ω).alloc b = S}) :
    ∃ x : ℝ, 0 < x ∧ x < B ∧
      ∑ S : Finset (Fin 2), (P {ω | (R ω).alloc ![x, B - x] = S}).toReal * pairValue S = 0 ∧
      OPT pairValue B ![x, B - x] = 1 := by sorry

end Supplement

end CompDesignBFM
