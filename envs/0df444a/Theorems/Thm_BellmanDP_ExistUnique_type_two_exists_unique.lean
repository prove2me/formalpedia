-- Prove2me | Theorems.Thm_BellmanDP_ExistUnique_type_two_exists_unique
-- name    : BellmanDP.ExistUnique.type_two_exists_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T16:02:22.290248+00:00
-- url     : https://prove2.me/theorems/0ff16d84-a540-4e41-b552-ae21192427dd
-- title:
--   Chapter IV, Theorem 2 — existence and uniqueness for equations of Type Two
-- statement:
--   Let $D \subseteq \mathbb{R}^N$, let $S$ be a nonempty set, and suppose the equation
--   $$f(p) = \sup_{q \in S}\big[g(p,q) + h(p,q)\,f(T(p,q))\big], \qquad p \in D,$$
--   is of Type Two: $g$ is bounded on bounded parts of $D$ uniformly in $q$; on each bounded part $|h| \le a < 1$; $T$ maps $D$ into $D$; and either $\|T(p,q)\| \le \|p\|$ or $D$ is bounded. Then:
--
--   1. there is a solution $f$ on $D$ that is bounded in every finite part of $D$, and any two such solutions agree on $D$;
--   2. the successive approximations $f_0(p) = \sup_q g(p,q)$, $f_{n+1}(p) = \sup_q[g(p,q) + h(p,q) f_n(T(p,q))]$ converge to $f(p)$ at every $p \in D$;
--   3. if $g$, $h$ and $T$ are continuous in $p$ on bounded portions of $D$, uniformly for all $q \in S$, then $f$ is continuous on every bounded portion $\{p \in D : \|p\| \le c\}$.
--
--   Type Two is the case in which each stage discounts the future by a factor bounded below one. Theorem 2 is the analogue of Theorem 1 for this case, with the class "bounded in any finite part of $D$" in place of "continuous and zero at $\theta$".
--
--   **Formalization Note** Uniqueness is asserted on $D$ only, since values of $f$ off $D$ are irrelevant. The book's "previous statements concerning continuity remain valid" is rendered as item 3, with "continuous in $p$ uniformly for all $q$" read as uniform equicontinuity on each bounded portion of $D$ (see the definition file).
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter IV, § 4, conditions (1a)-(1c), Theorem 2 and Eq. (4.3), p. 121

import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_SupEquation
import Definitions.Def_BellmanDP_ExistUnique_EquationTypes

open Filter Topology

namespace BellmanDP.ExistUnique

/-- Bellman, *Dynamic Programming*, Ch. IV, § 4, Theorem 2, p. 121. If
`f(p) = Sup_q [g(p, q) + h(p, q) f(T(p, q))]` is an equation of Type Two, there is a unique
solution on `D` which is bounded in any finite part of `D`; it is the limit of the successive
approximations (4.3) from `f₀(p) = Sup_q g(p, q)`; and it is continuous on every bounded portion
of `D` when `g`, `h`, `T` are continuous in `p` on bounded portions of `D` uniformly in `q`. -/
theorem type_two_exists_unique {N : ℕ} {S : Type*} [Nonempty S]
    (D : Set (EuclideanSpace ℝ (Fin N))) (g h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N))
    (hType : TypeTwo D g h T) :
    ∃ f : EuclideanSpace ℝ (Fin N) → ℝ,
      (BoundedOnBoundedParts D f ∧ ∀ p ∈ D, SolvesAt g h T f p) ∧
      (∀ F : EuclideanSpace ℝ (Fin N) → ℝ, BoundedOnBoundedParts D F →
        (∀ p ∈ D, SolvesAt g h T F p) → ∀ p ∈ D, F p = f p) ∧
      (∀ p ∈ D, Tendsto (fun n => succApprox g h T (supG g) n p) atTop (𝓝 (f p))) ∧
      (UnifContInP D g → UnifContInP D h → UnifContInP D T →
        ∀ c : ℝ, ContinuousOn f (D ∩ Metric.closedBall 0 c)) := by sorry

end BellmanDP.ExistUnique
