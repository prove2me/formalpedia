-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_phase_eq_of_forall_close_shift
-- name    : FiniteEnergyPlane.exists_phase_eq_of_forall_close_shift
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-29T21:34:38.054288+00:00
-- url     : https://prove2.me/theorems/b0cf4bc3-6b99-4f9f-a700-1167fe66251c
-- title:
--   A pointwise limit of maps uniformly close to phase shifts of a periodic map is a phase shift
-- statement:
--   Let $F$ be a normed group, $T>0$, and let $x:\mathbb{R}\to F$ be continuous and $T$-periodic. Fix $\kappa\in\mathbb{R}$, and let $f_j:\mathbb{R}\to F$ converge pointwise to $L:\mathbb{R}\to F$. Assume that for every $\varepsilon>0$ and all sufficiently large $j$ there is a phase $c_j\in\mathbb{R}$ with
--   $$\sup_{t\in\mathbb{R}}\|f_j(t)-x(\kappa t+c_j)\|\le\varepsilon .$$
--   Then there is $c\in\mathbb{R}$ with $L(t)=x(\kappa t+c)$ for all $t\in\mathbb{R}$.
--
--   Typical use: $f_j$ are loops on a contact manifold that converge to a limit loop and approach the reparametrizations of a fixed periodic Reeb orbit with a phase depending on $j$; the limit loop is then an exact reparametrization of that orbit.
--
--   **Formalization Note** Periodicity is `Function.Periodic x T`; pointwise convergence is `Tendsto (fun j => f j t) atTop (𝓝 (L t))` for each `t`; the supremum is written pointwise for all `t`.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: Asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996), 337–379, proof of Lemma 2.4

import Mathlib

namespace FiniteEnergyPlane

open Filter Topology

/-- Let `x : ℝ → F` be continuous and `T`-periodic with `T > 0`, let `κ : ℝ`, and let `f j → L`
pointwise. Suppose that for every `ε > 0`, for all large `j` some phase shift `t ↦ x(κ t + c)` is
uniformly `ε`-close to `f j`. Then `L` is itself a phase shift: `L t = x(κ t + c)` for some `c`. -/
theorem exists_phase_eq_of_forall_close_shift {F : Type*} [NormedAddCommGroup F] {x : ℝ → F}
    {T : ℝ} (hT : 0 < T) (hx : Continuous x) (hxT : Function.Periodic x T) (κ : ℝ)
    (f : ℕ → ℝ → F) (L : ℝ → F) (hf : ∀ t, Tendsto (fun j => f j t) atTop (𝓝 (L t)))
    (hclose : ∀ ε > 0, ∀ᶠ j in atTop, ∃ c : ℝ, ∀ t : ℝ, ‖f j t - x (κ * t + c)‖ ≤ ε) :
    ∃ c : ℝ, ∀ t : ℝ, L t = x (κ * t + c) := by
  sorry

end FiniteEnergyPlane
