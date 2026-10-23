-- Prove2me | Theorems.Thm_Bellman1957_ch4_thm1_type_one_pos_ratio_corrected
-- name    : Bellman1957.ch4_thm1_type_one_pos_ratio_corrected
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-23T01:31:45.863479+00:00
-- url     : https://prove2.me/theorems/302f533d-370c-483f-96e8-ce0f8de0e204
-- title:
--   Chapter IV, Theorem 1 with $a > 0$ (equations of Type One)
-- statement:
--   Let $D \subseteq \mathbb{R}^N$ (Euclidean norm) contain the null vector $\theta$, let $S$ be a nonempty set of decisions, and let $g, h : D \times S \to \mathbb{R}$, $T : D \times S \to D$. Suppose the equation
--
--   $$f(p) = \sup_{q \in S}\big[g(p,q) + h(p,q)\,f(T(p,q))\big] \quad (p \ne \theta), \qquad f(\theta) = 0,$$
--
--   is of Type One with a constant $a$ satisfying $0 < a < 1$. That is, $g$ is bounded on $\{p \in D : \|p\| \le c_1\}$ uniformly in $q$ for every $c_1$; $g(\theta, q) = 0$; $|h| \le 1$; $\|T(p,q)\| \le a\|p\|$; and $\sum_{n \ge 0} v(a^n c) < \infty$ for every $c \ge 0$, where $v(c) = \sup_{p \in D,\, \|p\| \le c}\sup_q |g(p,q)|$. Then:
--
--   1. there is exactly one solution on $D$ that is continuous at $\theta$ and equal to zero there;
--   2. it is the pointwise limit on $D$ of the approximations $f_0(p) = \sup_q g(p,q)$, $f_{n+1}(p) = \sup_q[g(p,q) + h(p,q) f_n(T(p,q))]$;
--   3. the same recursion started from any $f_0$ that is continuous at $\theta$, zero there, and bounded on bounded parts of $D$ also converges to it;
--   4. if $g$, $h$, $T$ are uniformly equicontinuous in $p$ on each bounded portion of $D$, uniformly in $q$, the solution is continuous on every bounded portion of $D$.
--
--   This is Theorem 1 of Chapter IV of Bellman's *Dynamic Programming* with the extra hypothesis $a > 0$. As printed (any $a < 1$), the theorem is false: for $a = 0$ condition (1e) no longer forces $v(c) \to 0$ as $c \to 0$, and the platform disproves the printed version (`BellmanDP.ExistUnique.type_one_exists_unique`). With $a > 0$, (1e) gives $v(a^n c) \to 0$, and since $v$ is monotone, $v(c) \to 0$, which is what the book's continuity argument uses.
--
--   **Formalization Note** Identical to the disproved theorem except for the hypothesis $0 < a$. Continuity at $\theta$ is continuity within $D$; the supremum in the equation is a genuine least upper bound (`IsLUB`); clause 4 uses uniform equicontinuity on bounded portions, as in the original formalization.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), doi:10.2307/j.ctv1nxcw0f, Chapter IV, § 3, conditions (1a)-(1e) and Theorem 1, pp. 119-120

import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_SupEquation
import Definitions.Def_BellmanDP_ExistUnique_EquationTypes

open Filter Topology BellmanDP.ExistUnique

theorem Bellman1957.ch4_thm1_type_one_pos_ratio_corrected {N : ℕ} {S : Type*} [Nonempty S]
    (D : Set (EuclideanSpace ℝ (Fin N))) (g h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N)) (a : ℝ)
    (hType : TypeOne D g h T a) (ha : 0 < a) :
    ∃ f : EuclideanSpace ℝ (Fin N) → ℝ,
      (ContinuousWithinAt f D 0 ∧ f 0 = 0 ∧ ∀ p ∈ D, p ≠ 0 → SolvesAt g h T f p) ∧
      (∀ F : EuclideanSpace ℝ (Fin N) → ℝ, ContinuousWithinAt F D 0 → F 0 = 0 →
        (∀ p ∈ D, p ≠ 0 → SolvesAt g h T F p) → ∀ p ∈ D, F p = f p) ∧
      (∀ p ∈ D, Tendsto (fun n => succApprox g h T (supG g) n p) atTop (𝓝 (f p))) ∧
      (∀ f₀ : EuclideanSpace ℝ (Fin N) → ℝ, ContinuousWithinAt f₀ D 0 → f₀ 0 = 0 →
        BoundedOnBoundedParts D f₀ →
        ∀ p ∈ D, Tendsto (fun n => succApprox g h T f₀ n p) atTop (𝓝 (f p))) ∧
      (UnifContInP D g → UnifContInP D h → UnifContInP D T →
        ∀ c : ℝ, ContinuousOn f (D ∩ Metric.closedBall 0 c)) := by sorry
