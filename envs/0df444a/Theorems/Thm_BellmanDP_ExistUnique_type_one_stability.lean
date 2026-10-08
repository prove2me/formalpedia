-- Prove2me | Theorems.Thm_BellmanDP_ExistUnique_type_one_stability
-- name    : BellmanDP.ExistUnique.type_one_stability
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T16:02:33.471748+00:00
-- url     : https://prove2.me/theorems/5eefa0e6-2d0b-4eae-a165-e8269103ffb6
-- title:
--   Chapter IV, Theorem 3 — stability of the solution of a Type One equation
-- statement:
--   Consider two equations of Type One with the same $h$, $T$ and constant $a$ and with rewards $g$ and $G$:
--   $$f(p) = \sup_q\big[g(p,q) + h(p,q) f(T(p,q))\big], \qquad F(p) = \sup_q\big[G(p,q) + h(p,q) F(T(p,q))\big], \qquad p \ne \theta,$$
--   and let $f$, $F$ be their solutions that vanish at $\theta$ and are continuous there. Put
--   $$u(c) = \sup_{p \in D,\ \|p\| \le c}\ \sup_q |G(p,q) - g(p,q)|.$$
--   Then for every $c$,
--   $$\sup_{p \in D,\ \|p\| \le c} |F(p) - f(p)| \le \sum_{n=0}^{\infty} u(a^n c).$$
--
--   The solution therefore depends continuously on the reward: a perturbation of $g$ that is small near $\theta$ changes the solution only slightly on each ball.
--
--   **Formalization Note** The supremum on the left is stated pointwise: for every $p \in D$ with $\|p\| \le c$. The series converges because $u(c) \le v_g(c) + v_G(c)$ and both equations satisfy (3.1e). $S$ is assumed nonempty.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter IV, § 6, Eqs. (6.1)-(6.5) and Theorem 3, Eq. (6.6), pp. 123-124

import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_SupEquation
import Definitions.Def_BellmanDP_ExistUnique_EquationTypes

namespace BellmanDP.ExistUnique

/-- Bellman, *Dynamic Programming*, Ch. IV, § 6, Theorem 3, p. 124. Let
`f(p) = Sup_q [g + h f(T)]` and `F(p) = Sup_q [G + h F(T)]` both be of Type One (same `h`, `T`,
`a`), and let `f`, `F` be their solutions vanishing at `θ` and continuous there. With
`u(c) = Sup_{‖p‖ ≤ c} Sup_q |G(p, q) − g(p, q)|`,
`Sup_{‖p‖ ≤ c} |F(p) − f(p)| ≤ Σ_{n=0}^∞ u(aⁿ c)`. -/
theorem type_one_stability {N : ℕ} {S : Type*} [Nonempty S]
    (D : Set (EuclideanSpace ℝ (Fin N))) (g G h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N)) (a : ℝ)
    (hg : TypeOne D g h T a) (hG : TypeOne D G h T a)
    (f F : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf_cont : ContinuousWithinAt f D 0) (hf_zero : f 0 = 0)
    (hf : ∀ p ∈ D, p ≠ 0 → SolvesAt g h T f p)
    (hF_cont : ContinuousWithinAt F D 0) (hF_zero : F 0 = 0)
    (hF : ∀ p ∈ D, p ≠ 0 → SolvesAt G h T F p) (c : ℝ) :
    ∀ p ∈ D, ‖p‖ ≤ c →
      |F p - f p| ≤ ∑' n : ℕ, radialSup D (fun p q => G p q - g p q) (a ^ n * c) := by sorry

end BellmanDP.ExistUnique
