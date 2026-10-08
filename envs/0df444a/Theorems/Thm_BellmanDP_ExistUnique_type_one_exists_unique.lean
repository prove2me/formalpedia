-- Prove2me | Theorems.Thm_BellmanDP_ExistUnique_type_one_exists_unique
-- name    : BellmanDP.ExistUnique.type_one_exists_unique
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-02T16:02:55.433042+00:00
-- url     : https://prove2.me/theorems/0cb90f0c-3da9-46ff-9ef1-a1285d5a9fa9
-- title:
--   Chapter IV, Theorem 1 — existence and uniqueness for equations of Type One
-- statement:
--   Let $D \subseteq \mathbb{R}^N$ (Euclidean norm), let $S$ be a nonempty set of decisions, and suppose the equation
--   $$f(p) = \sup_{q \in S}\big[g(p,q) + h(p,q)\,f(T(p,q))\big], \quad p \ne \theta, \qquad f(\theta) = 0,$$
--   is of Type One with constant $a$. That is, $\theta \in D$ and $T$ maps $D$ into $D$; $g$ is bounded on bounded parts of $D$ uniformly in $q$, with $g(\theta,q) = 0$; $|h| \le 1$; $\|T(p,q)\| \le a\|p\|$ with $0 \le a < 1$; and $\sum_{n=0}^\infty v(a^n c) < \infty$ for $v(c) = \sup_{\|p\| \le c}\sup_q |g(p,q)|$. Then:
--
--   1. there is exactly one solution on $D$ which is continuous at $p = \theta$ and equal to zero there;
--   2. this solution is the limit, at every $p \in D$, of the sequence
--   $$f_0(p) = \sup_q g(p,q), \qquad f_{n+1}(p) = \sup_q\big[g(p,q) + h(p,q)\,f_n(T(p,q))\big];$$
--   3. any initial function $f_0$ that is continuous at $\theta$, equal to zero there, and bounded on $\{p \in D : \|p\| \le c_1\}$ for every $c_1 > 0$ also yields, through the same recursion, a sequence converging to this solution at every $p \in D$;
--   4. if $g(p,q)$, $h(p,q)$ and $T(p,q)$ are continuous in $p$ in any bounded portion of $D$, uniformly for all $q \in S$, then the solution is continuous on every bounded portion $\{p \in D : \|p\| \le c\}$.
--
--   Type One equations describe processes in which every decision shrinks the state towards the null vector. The theorem is the general form of the existence and uniqueness results that Bellman proves for particular processes in Chapters I and II.
--
--   **Formalization Note** "Continuous at $p = \theta$" is continuity within $D$, and uniqueness is asserted on $D$. The supremum in the equation is a genuine least upper bound (`IsLUB`). The successive approximations use a real `iSup`, which is genuine here because the approximations stay bounded on bounded parts of $D$. Item 4 reads "continuous in $p$, uniformly for all $q$" as uniform equicontinuity on each bounded portion of $D$. For closed $D$ this coincides with the pointwise reading. For a non-closed $D$ the book's inductive step (a supremum over $q$ of the functions $f_n(T(\cdot,q))$ inherits continuity) is not supported by pointwise continuity. The requirement $a \ge 0$ loses no generality (see the definition of Type One).
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter IV, § 3, conditions (1a)-(1e) and Theorem 1, Eqs. (3.2)-(3.3), pp. 119-120

import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_SupEquation
import Definitions.Def_BellmanDP_ExistUnique_EquationTypes

open Filter Topology

namespace BellmanDP.ExistUnique

/-- Bellman, *Dynamic Programming*, Ch. IV, § 3, Theorem 1, pp. 119–120. For an equation
`f(p) = Sup_q [g(p, q) + h(p, q) f(T(p, q))]` (`p ≠ θ`), `f(θ) = 0`, of Type One:
1. there is exactly one solution on `D` that is continuous at `p = θ` (within `D`) and equal to
   zero there;
2. it is the limit of the successive approximations (3) started from `f₀(p) = Sup_q g(p, q)`;
3. any `f₀` continuous at `θ`, zero there, and bounded on `{p ∈ D : ‖p‖ ≤ c₁}` for every `c₁`
   also yields a sequence (3b) converging to it;
4. if `g`, `h`, `T` are continuous in `p` on bounded portions of `D`, uniformly for all `q ∈ S`,
   the solution is continuous on every bounded portion of `D`. -/
theorem type_one_exists_unique {N : ℕ} {S : Type*} [Nonempty S]
    (D : Set (EuclideanSpace ℝ (Fin N))) (g h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N)) (a : ℝ)
    (hType : TypeOne D g h T a) :
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

end BellmanDP.ExistUnique
