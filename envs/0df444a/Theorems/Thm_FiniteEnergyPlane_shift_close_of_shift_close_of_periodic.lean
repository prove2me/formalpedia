-- Prove2me | Theorems.Thm_FiniteEnergyPlane_shift_close_of_shift_close_of_periodic
-- name    : FiniteEnergyPlane.shift_close_of_shift_close_of_periodic
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-29T21:11:53.071806+00:00
-- url     : https://prove2.me/theorems/b2e08be7-7ec9-419b-a831-83ca804536e3
-- title:
--   Uniformly close shifts of a periodic function give uniformly close shifts of a dependent periodic function
-- statement:
--   Let $E,F$ be normed groups, $T>0$, and let $x:\mathbb{R}\to E$, $y:\mathbb{R}\to F$ be continuous and $T$-periodic. Assume every period of $x$ is a period of $y$: if $x(\tau+a)=x(\tau)$ for all $\tau$, then $y(\tau+a)=y(\tau)$ for all $\tau$. Then for every $\varepsilon>0$ there is $\delta>0$ such that for all $a,b\in\mathbb{R}$,
--   $$\sup_\tau\|x(\tau+a)-x(\tau+b)\|\le\delta\ \Longrightarrow\ \sup_\tau\|y(\tau+a)-y(\tau+b)\|\le\varepsilon .$$
--
--   Typical use: $y=x^{(m)}$ for a smooth periodic loop $x$ (possibly multiply covered, so $x$ need not be injective on a period), which turns uniform closeness of two phase shifts of $x$ into $C^m$ closeness.
--
--   **Formalization Note** Periodicity is `Function.Periodic`; the suprema are written pointwise for all $\tau$.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: Asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996), 337–379, proof of Theorem 1.3

import Mathlib

namespace FiniteEnergyPlane

open Filter Topology Set

/-- Let `x : ℝ → E` and `y : ℝ → F` be continuous and `T`-periodic, and suppose every period of
`x` is a period of `y`. Then shifts of `y` are uniformly close whenever the same shifts of `x` are
uniformly close. -/
theorem shift_close_of_shift_close_of_periodic {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {x : ℝ → E} {y : ℝ → F} {T : ℝ} (hT : 0 < T)
    (hx : Continuous x) (hy : Continuous y) (hxT : Function.Periodic x T)
    (hyT : Function.Periodic y T)
    (hper : ∀ a : ℝ, (∀ τ, x (τ + a) = x τ) → ∀ τ, y (τ + a) = y τ) :
    ∀ ε > 0, ∃ δ > 0, ∀ a b : ℝ, (∀ τ, ‖x (τ + a) - x (τ + b)‖ ≤ δ) →
      ∀ τ, ‖y (τ + a) - y (τ + b)‖ ≤ ε := by
  sorry

end FiniteEnergyPlane
