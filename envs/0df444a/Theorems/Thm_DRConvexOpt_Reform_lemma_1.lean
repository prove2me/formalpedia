-- Prove2me | Theorems.Thm_DRConvexOpt_Reform_lemma_1
-- name    : DRConvexOpt.Reform.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:34:39.619611+00:00
-- url     : https://prove2.me/theorems/65354ae1-1a1d-4496-8b2c-50cf67445eae
-- title:
--   Lemma 1, p. 34 — the semi-infinite constraint (12) over a strictly feasible conic confidence set holds iff dual multipliers φ_l ∈ K⋆ exist
-- statement:
--   Let $\mathcal K \subseteq \mathbb R^m$ be a proper cone, $C \in \mathbb R^{m \times P}$, $D \in \mathbb R^{m\times Q}$, $c \in \mathbb R^m$, and let
--   $$\mathcal C = \{(z,u) \in \mathbb R^P \times \mathbb R^Q : Cz + Du \preccurlyeq_{\mathcal K} c\}$$
--   be strictly feasible: some $(z,u)$ has $c - Cz - Du$ in the interior of $\mathcal K$. Let $v(x,z) = \max_{l \in \mathcal L} \big[(S_l z + s_l)^\top x + \mathbf t_l^\top z + t_l\big]$ satisfy (C3), and fix $x \in \mathbb R^N$, $f \in \mathbb R^P$, $g \in \mathbb R^Q$ and $h \in \mathbb R$. Then the semi-infinite constraint
--   $$v(x,z) + f^\top z + g^\top u \le h \qquad \forall (z,u) \in \mathcal C \tag{12}$$
--   holds if and only if there are $\phi_l \in \mathcal K^\star$, $l \in \mathcal L$, such that for all $l \in \mathcal L$
--   $$c^\top \phi_l + s_l^\top x + t_l \le h, \qquad C^\top \phi_l = S_l^\top x + \mathbf t_l + f, \qquad D^\top \phi_l = g.$$
--
--   The lemma replaces a constraint indexed by the infinitely many points of a confidence set by finitely many conic constraints; applied to each $\mathcal C_i$ it turns the dual of the moment problem into the finite system of Theorem 1.
--
--   **Formalization Note** The strict feasibility hypothesis is not printed in Lemma 1; its proof calls the $L$ maximization problems "strictly feasible", and conic strong duality with dual attainment needs it. Without it the statement can fail (for instance when the confidence set is a single point of the boundary of a second-order cone constraint). The scalar $t_l$ is `v.t0 l`, the vector $\mathbf t_l$ is `v.tv l`.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 34, Lemma 1 and (12)

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting

namespace DRConvexOpt.Reform

open MeasureTheory Matrix

/-- Lemma 1, p. 34: for a confidence set `{(z, u) : C z + D u ≼_K c}` with `K` a proper cone,
under the disclosed additional assumption that the set is strictly feasible, the semi-infinite
constraint (12) `v(x, z) + fᵀz + gᵀu ≤ h` on the set holds iff there are `φ_l ∈ K⋆`, `l ∈ ℒ`,
with `cᵀφ_l + s_lᵀx + t_l ≤ h`, `Cᵀφ_l = S_lᵀx + t_l + f` and `Dᵀφ_l = g`. -/
theorem lemma_1 {nP nQ nN nL m : ℕ} [NeZero nL]
    (C : Matrix (Fin m) (Fin nP) ℝ) (D : Matrix (Fin m) (Fin nQ) ℝ) (c : Fin m → ℝ)
    (K : Set (Fin m → ℝ)) (hK : IsProperCone K)
    (hslater : ∃ ω : (Fin nP → ℝ) × (Fin nQ → ℝ), c - (C *ᵥ ω.1 + D *ᵥ ω.2) ∈ interior K)
    (v : PWAff nN nP nL) (x : Fin nN → ℝ) (f : Fin nP → ℝ) (g : Fin nQ → ℝ) (h : ℝ) :
    (∀ ω ∈ confSet C D c K, v.eval x ω.1 + f ⬝ᵥ ω.1 + g ⬝ᵥ ω.2 ≤ h) ↔
    ∃ φ : Fin nL → Fin m → ℝ, ∀ l, φ l ∈ dualCone K ∧ c ⬝ᵥ φ l + v.s l ⬝ᵥ x + v.t0 l ≤ h ∧
      Cᵀ *ᵥ φ l = (v.S l)ᵀ *ᵥ x + v.tv l + f ∧ Dᵀ *ᵥ φ l = g := by sorry

end DRConvexOpt.Reform
