-- Prove2me | Theorems.Thm_DRConvexOpt_Reform_partition_step
-- name    : DRConvexOpt.Reform.partition_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:36:11.919531+00:00
-- url     : https://prove2.me/theorems/9cd041e7-2b69-4f39-b829-88afe9428766
-- title:
--   Proof of Theorem 1, p. 35 — under (N), the dual constraint on C_I is equivalent to the constraints on the pieces C̄_i with the sum over 𝒜(i)
-- statement:
--   Let the confidence sets $\mathcal C_i$ of (5) be defined by proper cones, let $\mathcal C_I$ be bounded and contain every $\mathcal C_i$, assume the nesting condition (N), and assume $P + Q \ge 1$. Let $v$ satisfy (C3) and fix $x$, $\beta \in \mathbb R^K$ and $\kappa, \lambda \in \mathbb R^I$. With $\overline{\mathcal C}_i = \mathcal C_i \setminus \bigcup_{i' \in \mathcal D(i)} \mathcal C_{i'}$, the constraint
--   $$[Az + Bu]^\top \beta + \sum_{i \in \mathcal I} \mathbf 1_{[(z,u) \in \mathcal C_i]}[\kappa_i - \lambda_i] \ge v(x,z) \quad \forall (z,u) \in \mathcal C_I$$
--   holds if and only if
--   $$[Az + Bu]^\top \beta + \sum_{i' \in \mathcal A(i)}[\kappa_{i'} - \lambda_{i'}] \ge v(x,z) \quad \forall (z,u) \in \overline{\mathcal C}_i,\ \forall i \in \mathcal I.$$
--
--   Under (N) the sets $\overline{\mathcal C}_i$ cover $\mathcal C_I$ and on $\overline{\mathcal C}_i$ the confidence sets containing a point are exactly those indexed by $\mathcal A(i)$, so the indicator sum becomes a constant on each piece.
--
--   **Formalization Note** Two hypotheses are added. $\mathcal C_i \subseteq \mathcal C_I$ for all $i$ is what "partition the support $\mathcal C_I$" presupposes (under the assumptions of Theorem 1 it follows from (S1)). $P + Q \ge 1$ excludes the zero-dimensional space, where $\mathcal C_I$ is a single point that is strictly included in itself, so $\overline{\mathcal C}_I = \emptyset$ and the equivalence fails. The paper's "nonempty" pieces are not stated.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 35, proof of Theorem 1: the partition of C_I into the sets C̄_i

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting

namespace DRConvexOpt.Reform

open MeasureTheory Matrix

/-- Proof of Theorem 1, p. 35: under (N), the constraint of the dual moment problem on `C_I` is
equivalent to the constraint set over the pieces `C̄_i = C_i \ ⋃_{i' ∈ 𝒟(i)} C_{i'}`, with the
indicator sum replaced by the sum over the antecedents `𝒜(i)`. Disclosed additions: every `C_i` lies
in `C_I` (what "partition the support `C_I`" presupposes) and `P + Q > 0`. -/
theorem partition_step {nP nQ nK nI nN nL : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (v : PWAff nN nP nL)
    (hK : ∀ i, IsProperCone (d.K i))
    (hbdd : Bornology.IsBounded (d.conf (Fin.last nI)))
    (hN : Nesting d) (hsub : ∀ i, d.conf i ⊆ d.conf (Fin.last nI)) (hdim : 0 < nP + nQ)
    (x : Fin nN → ℝ) (β : Fin nK → ℝ) (κ lam : Fin (nI + 1) → ℝ) :
    (∀ ω ∈ d.conf (Fin.last nI),
        v.eval x ω.1 ≤ (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ⬝ᵥ β +
          ∑ i, (d.conf i).indicator (fun _ => (1 : ℝ)) ω * (κ i - lam i)) ↔
    ∀ i, ∀ ω ∈ cbar d i,
      v.eval x ω.1 ≤ (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ⬝ᵥ β + ∑ i' ∈ anc d i, (κ i' - lam i') := by sorry

end DRConvexOpt.Reform
