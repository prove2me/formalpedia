-- Prove2me | Theorems.Thm_ApproxVI_equilibrium_set
-- name    : ApproxVI.equilibrium_set
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:16:04.56401+00:00
-- url     : https://prove2.me/theorems/d597d4d0-d33f-46fe-8590-b7fd8fd1f202
-- title:
--   §5, p.15 — the equilibrium set $\{J : \|TJ-J\|_\nu\le\epsilon\}$ of $\tilde TJ-J$
-- statement:
--   Let $\nu$ be positive weights, $0<\alpha<1$, $T$ satisfy (AV1), $J^*$ a fixed point of $T$, and $\epsilon>0$. Then:
--
--   1. for every $J$, $J\in\tilde TJ$ iff $\|TJ-J\|_\nu\le\epsilon$, and $0\in\tilde TJ-J$ iff $\|TJ-J\|_\nu\le\epsilon$; so the equilibrium set of $\tilde TJ-J$ is
--
--   $$
--   \mathcal A=\{J\in\mathbb R^d:\ \|TJ-J\|_\nu\le\epsilon\};
--   $$
--
--   2. $J^*\in\mathcal A$;
--   3. $\mathcal A$ is closed;
--   4. $\mathcal A$ is a neighbourhood of $J^*$.
--
--   The printed Theorem 2 claims convergence into $\mathcal A$; this item records the facts about $\mathcal A$ stated before it.
--
--   **Formalization Note** $J^*$ is a variable with $TJ^*=J^*$; by (AV1) it is the unique fixed point. $\tilde TJ-J$ is the image of $\tilde TJ$ under $y\mapsto y-J$.
--
--   Differences from the source:
--   - generalization: T is the Bellman operator (3), contractive by (AV1) → T is any map ℝ^d → ℝ^d satisfying (AV1); reason: the argument uses only (AV1); the Bellman operator under (AV1) is an instance
--   - generalization: §5 assumes (AV1)–(AV5) throughout → only (AV1) with a fixed point J* is assumed; reason: the statement involves no errors, step sizes or noise; the other assumptions do not enter
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, §5, p.15, "the equilibrium set of T̃J − J is given by A = {J | ∥TJ − J∥ν ≤ ε}"

import Mathlib
import Definitions.Def_ApproxVI_Ttilde

namespace ApproxVI

open Topology

/-- **The equilibrium set of `T̃J − J`**, Ramaswamy & Bhatnagar, *Analyzing Approximate Value
Iteration Algorithms*, arXiv:1709.04673v5, §5, p.15: `J` is a fixed point of the perturbed
Bellman operator `T̃`, or an equilibrium point of the `T̃J − J` operator (the origin belongs
to `T̃J − J`), iff `‖TJ − J‖_ν ≤ ε`. In other words the equilibrium set of `T̃J − J` is
`A = {J | ‖TJ − J‖_ν ≤ ε}`. Since `J* ∈ A` and `T` is continuous, `A` is a closed
neighborhood of `J*`.

Hypotheses: (AV1) (§3.1, p.7) and `J*` the fixed point of `T`.

**Formalization Note** `T` is any map satisfying (AV1); `J*` is a binder with `T J* = J*`
(the fixed point is unique by (AV1)). "Neighborhood" is `A ∈ 𝓝 J*`. -/
theorem equilibrium_set {d : ℕ} (ν : Fin d → ℝ) (hν : ∀ i, 0 < ν i) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (T : (Fin d → ℝ) → (Fin d → ℝ))
    (hT : ∀ x y, wNorm ν (T x - T y) ≤ α * wNorm ν (x - y))
    (Jstar : Fin d → ℝ) (hJstar : T Jstar = Jstar) (ε : ℝ) (hε : 0 < ε) :
    (∀ J, (J ∈ Ttilde ν T ε J ↔ wNorm ν (T J - J) ≤ ε) ∧
        ((0 : Fin d → ℝ) ∈ (fun y => y - J) '' Ttilde ν T ε J ↔ wNorm ν (T J - J) ≤ ε)) ∧
      Jstar ∈ {J | wNorm ν (T J - J) ≤ ε} ∧
      IsClosed {J | wNorm ν (T J - J) ≤ ε} ∧
      {J | wNorm ν (T J - J) ≤ ε} ∈ 𝓝 Jstar := by sorry

end ApproxVI
