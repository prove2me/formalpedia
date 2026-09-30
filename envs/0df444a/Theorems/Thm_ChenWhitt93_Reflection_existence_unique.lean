-- Prove2me | Theorems.Thm_ChenWhitt93_Reflection_existence_unique
-- name    : ChenWhitt93.Reflection.existence_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:14:43.773181+00:00
-- url     : https://prove2.me/theorems/b9028fdb-59b9-4450-bf79-71c717713acb
-- title:
--   Section 2, (2.1)–(2.3) — the reflection $(\psi(x),\phi(x))$ exists and is unique
-- statement:
--   Let $Q$ be an $n\times n$ matrix such that $Q^{\mathsf t}$ is substochastic and $Q^k \to 0$, let $T \in \mathbb R$, and let $x \in D([0,T],\mathbb R^n)$ with $x(0) \ge 0$ componentwise. Then, as noted by Harrison and Reiman and re-derived in the paper through Proposition 2.2, there is a pair $(y,z)$ with $y \in D([0,T],\mathbb R^n)$ satisfying (2.1)–(2.3), and it is unique on $[0,T]$:
--   $$
--   (y,z),\ (y',z') \text{ both satisfy (2.1)–(2.3)} \implies y(t) = y'(t),\ z(t) = z'(t) \quad (0 \le t \le T).
--   $$
--
--   This is what makes $(\psi,\phi)$ a map, and it shows that the Lipschitz bounds of the mission, stated for all solution pairs, are not vacuous.
--
--   **Formalization Note** Conditions (2.1)–(2.2) force $z(0) = x(0)$, so $x(0) \ge 0$ is necessary for a solution to exist; the paper, which works with processes starting at nonnegative values, leaves this implicit. It is the only hypothesis added relative to the page. Paths are functions $\mathbb R \to \mathbb R^n$ of which only the restriction to $[0,T]$ matters; $x \in D([0,T],\mathbb R^n)$ is the predicate `IsCadlagOn`. A pair $(y,z)$ with `IsReflection Q T x y z` is exactly a pair $(\psi(x),\phi(x))$; the theorem is stated for every such pair, so no choice of the map is involved.
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), p. 337, Section 2, definition of the reflection map (2.1)–(2.3); p. 338, 'This proves that there is a unique ψ(x) associated with each x'

import Mathlib
import Definitions.Def_ChenWhitt93_Reflection_Basic
import Definitions.Def_ChenWhitt93_Reflection_ReflectionMap

open Filter Topology Matrix

namespace ChenWhitt93.Reflection

/-- Section 2, p. 337: the reflection map associated with `Q` sends `x ∈ D([0,T], ℝⁿ)`
into a unique `(y, z) = (ψ(x), φ(x))` satisfying (2.1)–(2.3). Since (2.1)–(2.2) force
`z(0) = x(0) ≥ 0`, a solution exists only when `x(0) ≥ 0`, which is assumed here. -/
theorem existence_unique {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : IsTransientSubstochasticT Q) (T : ℝ) (x : ℝ → Fin n → ℝ)
    (hx : IsCadlagOn T x) (hx0 : 0 ≤ x 0) :
    (∃ y z : ℝ → Fin n → ℝ, IsReflection Q T x y z) ∧
    ∀ y z y' z' : ℝ → Fin n → ℝ, IsReflection Q T x y z → IsReflection Q T x y' z' →
      ∀ t ∈ Set.Icc (0 : ℝ) T, y t = y' t ∧ z t = z' t := by sorry

end ChenWhitt93.Reflection
