-- Prove2me | Theorems.Thm_AGT_clarke_pivot_properties
-- name    : AGT.clarke_pivot_properties
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T03:08:32.854222+00:00
-- url     : https://prove2.me/theorems/a9cb4a4b-d335-4d73-84f0-0533b89c3ac1
-- title:
--   Clarke pivot payments: no positive transfers, individual rationality
-- statement:
--   The Clarke pivot rule makes no positive transfers, and is individually rational when valuations are nonnegative (Lemma 9.20 of *Algorithmic Game Theory*). Let $f$ be any welfare-maximizing choice rule on the domain, and charge each player the Clarke payment $p_i(v) = \max_b \sum_{j\ne i} v_j(b) - \sum_{j\ne i} v_j(f(v))$ — the externality they impose on the others. Then:
--
--   1. no player is ever paid money: $p_i(v) \ge 0$ on every profile of the domain;
--   2. if every valuation in every domain is pointwise nonnegative, every player's utility $v_i(f(v)) - p_i(v)$ is nonnegative on every profile of the domain.
--
--   *A note on the hypotheses.* $A$ is finite and nonempty so the Clarke maximum is attained (`Finset.sup'`); combined with Theorem 9.17 this yields the standard "VCG with Clarke pivot" mechanism: truthful, individually rational, and never subsidizing.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 9.3.4, Lemma 9.20, pp. 219-220

import Definitions.Def_agt_mechanism

namespace AGT

/-- The Clarke pivot rule makes no positive transfers, and is individually
rational when valuations are nonnegative (Lemma 9.20 of *Algorithmic Game
Theory*).  `f` is any welfare-maximizing choice rule on the domain `V`;
with the Clarke payments `pᵢ = max_b ∑_{j≠i} vⱼ(b) − ∑_{j≠i} vⱼ(f(v))`,
every payment is nonnegative, and if every valuation in every domain is
pointwise nonnegative then every player's utility is nonnegative as well.
Finiteness and nonemptiness of `A` make the Clarke maximum attained. -/
theorem clarke_pivot_properties {A ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] [Nonempty A] (V : ι → Set (A → ℝ))
    (f : (ι → A → ℝ) → A) (hf : MaximizesWelfare V f) :
    NoPositiveTransfers V f (clarkePayment f) ∧
      ((∀ i, ∀ vi ∈ V i, ∀ a, 0 ≤ vi a) →
        IndividuallyRational V f (clarkePayment f)) := by
  sorry

end AGT
