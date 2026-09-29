-- Prove2me | Theorems.Thm_ContinuousLinearMap_exists_comp_torusEmb_eq_and_cylinder_noAtomicMass_of_box_noAtomicMass
-- name    : ContinuousLinearMap.exists_comp_torusEmb_eq_and_cylinder_noAtomicMass_of_box_noAtomicMass
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/e8323cf8-43dd-5541-a73b-d252a63d704b
-- title:
--   Pushing a box-atomless functional from the torus to (ℂ×ℂ)ᵈ
-- statement:
--   Fix $d\in\mathbb N$, a subset $XK\subseteq(\mathbb C\times\mathbb C)^{\mathrm{Fin}\,d}$, and a continuous map $\mathrm{emb}$ from the torus $(\mathrm{AddCircle}\,1)^{\mathrm{Fin}\,d}$ into $XK$ whose $i$-th coordinate is prescribed by $\mathrm{emb}(\theta)_i=(\mathrm{fourier}\,1(\theta_i),\mathrm{fourier}\,(-1)(\theta_i))$, i.e. $(e^{2\pi i\theta_i},e^{-2\pi i\theta_i})$. Let $\mu$ be a continuous $\mathbb C$-linear functional on $C((\mathrm{AddCircle}\,1)^{\mathrm{Fin}\,d},\mathbb C)$ which is atomless on boxes in the following sense: for every $\tau$ in the torus and every $\varepsilon>0$ there are open sets $U_i\subseteq\mathrm{AddCircle}\,1$ with $\tau_i\in U_i$ such that every continuous $g$ with $\|g\|_\infty\le 1$ vanishing at each point $\theta$ having some coordinate $\theta_i\notin U_i$ satisfies $\|\mu g\|<\varepsilon$. The conclusion asserts the existence of a continuous $\mathbb C$-linear functional $\Lambda$ on $C(XK,\mathbb C)$ such that $\Lambda h=\mu(h\circ\mathrm{emb})$ for all $h$, and such that $\Lambda$ is atomless on cylinders: for every $\tau\in(\mathbb C\times\mathbb C)^{\mathrm{Fin}\,d}$ — arbitrary, not required to lie in $XK$ — and every $\varepsilon>0$ there are open sets $U_v\subseteq\mathbb C\times\mathbb C$ with $\tau_v\in U_v$ for all $v$, such that every $g\in C(XK,\mathbb C)$ with $\|g\|_\infty\le 1$ vanishing at each $y\in XK$ having some coordinate $y_v\notin U_v$ satisfies $\|\Lambda g\|<\varepsilon$.
--
--   This is the transfer step between two coordinate frames for measures on Satake/Hecke parameters: the torus frame, in which boxes are products of arcs, and the frame of $(t,t^{-1})$-pairs in $(\mathbb C\times\mathbb C)^d$, in which the relevant neighbourhoods are cylinders over open subsets of $\mathbb C\times\mathbb C$. It is used by [`AutomorphicForm.exists_clm_cylinder_noAtomicMass_and_apply_monomial_eq_sum_laurentCoeff_mul_of_box_noAtomicMass`](thm.html#AutomorphicForm.exists_clm_cylinder_noAtomicMass_and_apply_monomial_eq_sum_laurentCoeff_mul_of_box_noAtomicMass), where the functional must be presented in the cylinder frame while its atomlessness has been established on the torus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ContinuousLinearMap_exists_comp_torusEmb_eq_and_cylinder_noAtomicMass_of_box_noAtomicMass.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem ContinuousLinearMap.exists_comp_torusEmb_eq_and_cylinder_noAtomicMass_of_box_noAtomicMass
    (d : ℕ) (XK : Set (Fin d → ℂ × ℂ))
    (emb : C((Fin d → AddCircle (1 : ℝ)), XK))
    (hemb : ∀ (θ : Fin d → AddCircle (1 : ℝ)) (i : Fin d),
      ((emb θ : XK) : Fin d → ℂ × ℂ) i = ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ)))
    (μ : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ)
    (hμ : ∀ (τ : Fin d → AddCircle (1 : ℝ)), ∀ ε > (0 : ℝ),
        ∃ U : Fin d → Set (AddCircle (1 : ℝ)), (∀ i, IsOpen (U i) ∧ τ i ∈ U i) ∧
          ∀ g : C((Fin d → AddCircle (1 : ℝ)), ℂ),
            (∀ θ, (∃ i, θ i ∉ U i) → g θ = 0) → (∀ θ, ‖g θ‖ ≤ 1) → ‖μ g‖ < ε) :
    ∃ Λ : C(XK, ℂ) →L[ℂ] ℂ,
      (∀ h : C(XK, ℂ), Λ h = μ (h.comp emb)) ∧
      ∀ (τ : Fin d → ℂ × ℂ), ∀ ε > (0 : ℝ), ∃ U : Fin d → Set (ℂ × ℂ),
        (∀ v ∈ (Finset.univ : Finset (Fin d)), IsOpen (U v) ∧ τ v ∈ U v) ∧
        ∀ g : C(XK, ℂ), (∀ y : XK, (∃ v ∈ (Finset.univ : Finset (Fin d)), (y : Fin d → ℂ × ℂ) v ∉ U v) → g y = 0) →
          (∀ y, ‖g y‖ ≤ 1) → ‖Λ g‖ < ε := by sorry
