-- Prove2me | Theorems.Thm_AGT_wmon_implies_ic_convex
-- name    : AGT.wmon_implies_ic_convex
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-13T03:09:00.292178+00:00
-- url     : https://prove2.me/theorems/8b0c19ab-971c-4c58-aa25-a668c9b7564a
-- title:
--   Weak monotonicity implements on convex domains (Saks-Yu)
-- statement:
--   On convex domains, weak monotonicity suffices for implementability (Theorem 9.29 of *Algorithmic Game Theory*, sufficiency half — Saks–Yu). If every domain $V_i$ is a convex subset of $\mathbb{R}^A$ with $A$ finite, and the choice rule $f$ is weakly monotone, then there exist payment functions $p$ making the mechanism $(f, p)$ incentive compatible.
--
--   *A note on the status and hypotheses.* The book states this half without proof ("quite involved"); the reference proof is Saks–Yu (2005), so this milestone carries a genuinely hard formalization with a published paper proof. Convexity is essential — the book notes WMON is not sufficient on general (non-simply-connected) domains — and $A$ finite is the Saks–Yu setting.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 9.5.3, Theorem 9.29 (sufficiency; Saks-Yu 2005), p. 227

import Definitions.Def_agt_mechanism

namespace AGT

/-- On convex domains, weak monotonicity suffices for implementability
(Theorem 9.29 of *Algorithmic Game Theory*, sufficiency half;
Saks–Yu).  If every domain `V i` is a convex subset of the finite-
dimensional space `A → ℝ` and the choice rule `f` is weakly monotone, then
payment functions exist making `(f, p)` incentive compatible.  Convexity is
essential: the book notes WMON is not sufficient on general (non-simply-
connected) domains. -/
theorem wmon_implies_ic_convex {A ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] (V : ι → Set (A → ℝ)) (hconv : ∀ i, Convex ℝ (V i))
    (f : (ι → A → ℝ) → A) (hmon : WeakMonotone V f) :
    ∃ p : ι → (ι → A → ℝ) → ℝ, MechIncentiveCompatible V f p := by
  sorry

end AGT
