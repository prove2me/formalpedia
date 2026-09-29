-- Prove2me | Theorems.Thm_AGT_ttc_strategyproof
-- name    : AGT.ttc_strategyproof
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T03:11:41.839399+00:00
-- url     : https://prove2.me/theorems/84310e09-e8e3-48c6-bc89-84e2d32e9f9f
-- title:
--   The Top Trading Cycle mechanism is strategy-proof (Roth)
-- statement:
--   The Top Trading Cycle mechanism is strategy-proof (Theorem 10.7 of *Algorithmic Game Theory*; Roth). Formally: let $F$ be any mechanism that, on every profile of strict preferences, selects a core allocation — by Theorem 10.6 the core is a single point, the TTC outcome, so $F$ is pinned down on valid profiles. Then no agent can misreport her ordering and receive a house she truly prefers: for every profile, every agent $i$, and every alternative strict ordering, the house $F$ gives $i$ after the misreport either equals or is truly-worse than the house $F$ gives her under truth.
--
--   *A note on the rendering.* Stating the theorem for every core-selecting $F$, with the misreport quantified after $F$, is what makes it a statement about the mechanism rather than about one run of an algorithm; nothing is chosen with hindsight.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 10.3, Theorem 10.7, p. 255

import Definitions.Def_agt_matching

namespace AGT

/-- The Top Trading Cycle mechanism is strategy-proof (Theorem 10.7 of
*Algorithmic Game Theory*; Roth).  Formally: any mechanism selecting, on
every profile of strict preferences, the unique core allocation (Theorem
10.6 — the TTC outcome) leaves no agent able to obtain a house they truly
prefer by misreporting their ordering. -/
theorem ttc_strategyproof {N : Type*} [Fintype N] [DecidableEq N]
    (F : (N → N → N → Prop) → N ≃ N)
    (hF : ∀ P, IsPrefProfile P → ¬ HouseBlocked P (F P)) :
    ∀ P, IsPrefProfile P → ∀ i (r' : N → N → Prop),
      IsStrictTotalOrder N r' →
        F (Function.update P i r') i = F P i ∨
          P i (F P i) (F (Function.update P i r') i) := by
  sorry

end AGT
