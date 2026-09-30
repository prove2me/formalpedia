-- Prove2me | Theorems.Thm_ChenWhitt93_Reflection_remark_2_1_tight
-- name    : ChenWhitt93.Reflection.remark_2_1_tight
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:42:12.047594+00:00
-- url     : https://prove2.me/theorems/20a87ec3-6503-43c6-acfd-f347d333e9ea
-- title:
--   Remark (2.1) — the bounds are tight for $Q = 0$, $n = 1$
-- statement:
--   Take $n = 1$, $Q = 0$, $T = 1$, $x_1(t) = 0$ for $0 \le t \le 1$ and
--   $$
--   x_2(t) = -\mathbf 1_{[1/3,1/2)}(t) + \mathbf 1_{[1/2,1]}(t).
--   $$
--   Both paths lie in $D([0,1],\mathbb R)$, both have reflections, and for any reflections $(\psi(x_i),\phi(x_i))$,
--   $$
--   \|x_1 - x_2\| = \|x_2\| = 1, \qquad \|\phi(x_1) - \phi(x_2)\| = \|\phi(x_2)\| = 2, \qquad \|\psi(x_1) - \psi(x_2)\| = \|\psi(x_2)\| = 1 .
--   $$
--   For $Q = 0$ the bounds of Propositions 2.1 and 2.3 read $\|\psi(x_1) - \psi(x_2)\| \le \|x_1 - x_2\|$ and $\|\phi(x_1) - \phi(x_2)\| \le 2\|x_1 - x_2\|$, so this example shows that both are attained.
--
--   **Formalization Note** In dimension $1$ the sup norm is the only candidate, so the correction to (2.6) plays no role here. The paths are functions on $\mathbb R$ restricted to $[0,1]$.
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), pp. 340–341, Remark (2.1)

import Mathlib
import Definitions.Def_ChenWhitt93_Reflection_Basic
import Definitions.Def_ChenWhitt93_Reflection_ReflectionMap

open Filter Topology Matrix

namespace ChenWhitt93.Reflection

/-- Remark (2.1) (pp. 340–341): for `n = 1`, `Q = 0`, `T = 1`, `x₁ ≡ 0` and
`x₂ = −1_{[1/3,1/2)} + 1_{[1/2,1]}`, the reflections exist and
`‖x₁ − x₂‖ = ‖x₂‖ = 1`, `‖φ(x₁) − φ(x₂)‖ = ‖φ(x₂)‖ = 2`, `‖ψ(x₁) − ψ(x₂)‖ = ‖ψ(x₂)‖ = 1`. -/
theorem remark_2_1_tight :
    let x₁ : ℝ → Fin 1 → ℝ := fun _ _ => 0
    let x₂ : ℝ → Fin 1 → ℝ := fun t _ =>
      -(Set.indicator (Set.Ico (1 / 3 : ℝ) (1 / 2)) (fun _ => (1 : ℝ)) t) +
        Set.indicator (Set.Icc (1 / 2 : ℝ) 1) (fun _ => (1 : ℝ)) t
    IsCadlagOn 1 x₁ ∧ IsCadlagOn 1 x₂ ∧
    sumSupNorm 1 (x₁ - x₂) = 1 ∧ sumSupNorm 1 x₂ = 1 ∧
    (∃ y z : ℝ → Fin 1 → ℝ, IsReflection (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 x₁ y z) ∧
    (∃ y z : ℝ → Fin 1 → ℝ, IsReflection (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 x₂ y z) ∧
    ∀ y₁ z₁ y₂ z₂ : ℝ → Fin 1 → ℝ,
      IsReflection (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 x₁ y₁ z₁ →
      IsReflection (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 x₂ y₂ z₂ →
      sumSupNorm 1 (z₁ - z₂) = 2 ∧ sumSupNorm 1 z₂ = 2 ∧
      sumSupNorm 1 (y₁ - y₂) = 1 ∧ sumSupNorm 1 y₂ = 1 := by sorry

end ChenWhitt93.Reflection
