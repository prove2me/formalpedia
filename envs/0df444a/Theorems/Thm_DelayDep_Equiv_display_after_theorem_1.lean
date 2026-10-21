-- Prove2me | Theorems.Thm_DelayDep_Equiv_display_after_theorem_1
-- name    : DelayDep.Equiv.display_after_theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:01.99929+00:00
-- url     : https://prove2.me/theorems/3013dce0-4d73-42d1-a51c-133eb5852a03
-- title:
--   p. 3349, display after the proof of Theorem 1 — Ψ̄^en(x,z) F̄^en_T(z) = ∫_z^∞∫_x^∞ f^ex(u,v) du dv, decreasing in x and z
-- statement:
--   Let $f$ be a joint pdf on $\mathbb R_+^2$ of (service time, patience time), and let $(f^{en}_T, \psi^{en})$ be given by (1): $f^{en}_T = f^{ex}_T$ and $\psi^{en}(x,z) = \int_z^\infty f(x,y)\,dy \big/ \int_z^\infty f^{ex}_T(y)\,dy$. Write $\Psi^{en}(x,z) = \int_0^x \psi^{en}(u,z)\,du$, $\bar\Psi^{en} = 1 - \Psi^{en}$ and $\bar F^{en}_T(z) = \int_z^\infty f^{en}_T(y)\,dy$. Then for all $x, z \ge 0$
--   $$\bar\Psi^{en}(x,z)\,\bar F^{en}_T(z) = \int_{v=z}^\infty \int_{u=x}^\infty f(u,v)\,du\,dv,$$
--   and the right-hand side is nonincreasing in $x \in [0,\infty)$ for each fixed $z \ge 0$, and nonincreasing in $z \in [0,\infty)$ for each fixed $x \ge 0$.
--
--   In probabilistic terms, $P(S^{en}(z) > x)\,P(T^{en} > z) = P(S^{ex} > x, T^{ex} > z)$: the two dependence mechanisms agree on the service-time law of served customers. Theorem 2 of the paper is built on this monotonicity.
--
--   **Formalization Note** No condition on the patience tail is needed: where $\bar F^{en}_T(z) = 0$ both sides vanish (Lean's $\psi^{en}$ is $0$ there). "Decreasing" is read as nonincreasing (`AntitoneOn` on $[0,\infty)$).
-- source:
--   Wu, Bassamboo & Perry, When service times depend on customers’ delays, Operations Research 70(6) (2022), p. 3349 (PDF 6), unnumbered display after the proof of Theorem 1

import Mathlib
import Definitions.Def_DelayDep_Equiv_Model

namespace DelayDep.Equiv

open MeasureTheory

/-- The display after the proof of Theorem 1, p. 3349: under (1), for `x, z ≥ 0`,
`Ψ̄^en(x, z) F̄^en_T(z) = ∫_{v=z}^∞ ∫_{u=x}^∞ f^ex(u, v) du dv`, where
`Ψ^en(x, z) = ∫_0^x ψ^en(u, z) du` and `F̄^en_T(z) = ∫_z^∞ f^ex_T`; and the right-hand side is
decreasing in `x` and in `z` on `[0, ∞)`. -/
theorem display_after_theorem_1 (f : ℝ → ℝ → ℝ) (hf : IsJointPdf f) :
    (∀ x z : ℝ, 0 ≤ x → 0 ≤ z →
      (1 - ∫ u in Set.Icc 0 x, psiEn f u z) * tailT f z =
        ∫ v in Set.Ioi z, ∫ u in Set.Ioi x, f u v) ∧
    (∀ z : ℝ, 0 ≤ z →
      AntitoneOn (fun x => ∫ v in Set.Ioi z, ∫ u in Set.Ioi x, f u v) (Set.Ici 0)) ∧
    (∀ x : ℝ, 0 ≤ x →
      AntitoneOn (fun z => ∫ v in Set.Ioi z, ∫ u in Set.Ioi x, f u v) (Set.Ici 0)) := by sorry

end DelayDep.Equiv
