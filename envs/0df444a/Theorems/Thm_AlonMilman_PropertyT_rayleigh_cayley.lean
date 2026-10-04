-- Prove2me | Theorems.Thm_AlonMilman_PropertyT_rayleigh_cayley
-- name    : AlonMilman.PropertyT.rayleigh_cayley
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:33:53.597911+00:00
-- url     : https://prove2.me/theorems/6fd7d0c5-d6eb-4e20-91a2-1da2b49b764b
-- title:
--   Proof of Lemma 4.8 — Rayleigh's principle: λ₁ of a Cayley multigraph is the minimum of (Qy, y) on zero-sum unit vectors
-- statement:
--   Let $\phi : H \to T$ be a homomorphism from a group $H$ to a finite group $T$ with $|T| \ge 2$, and let $S \subseteq H$ be finite with $S = S^{-1}$. Let $G = G(T, \phi(S))$ be the Cayley multigraph, $Q = Q_G = |S|\cdot I - \sum_{s\in S}\pi(\phi(s))$ its matrix and $\lambda_1(G)$ the second-smallest eigenvalue of $Q$ counted with multiplicity. Let $W = \{ y \in \mathbb{R}^T : \sum_{t} y_t = 0 \}$. Then the minimum
--
--   $$\min\big\{ (Qy, y) : y \in W,\ \|y\| = 1 \big\}$$
--
--   exists and equals $\lambda_1(G)$.
--
--   This is Rayleigh's principle as used at the end of the proof of Lemma 4.8: the lower bound on $(Qy,y)$ over $W$ obtained from Lemma 4.7 becomes a lower bound on $\lambda_1(G)$.
--
--   **Formalization Note** "Minimum" is stated as `IsLeast`: $\lambda_1(G)$ belongs to the set of values $(Qy,y)$ and is a lower bound for it. The norm is the Euclidean one, $\|y\|^2 = \sum_t y_t^2$.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 85, proof of Lemma 4.8 (Rayleigh's principle)

import Mathlib
import Definitions.Def_AlonMilman_PropertyT_lambda1
import Definitions.Def_AlonMilman_PropertyT_laplacian
import Definitions.Def_AlonMilman_PropertyT_cayleyMultigraph

open Matrix

namespace AlonMilman.PropertyT

/-- Rayleigh's principle for the Cayley multigraph (Alon–Milman 1985, proof of Lemma 4.8,
p. 85): for `S = S⁻¹` finite and `|T| ≥ 2`, `λ₁` of the Cayley multigraph `G(T, φ(S))` is the
minimum of `(Q y, y)` over real vectors `y` with coordinate sum `0` and `‖y‖ = 1`. -/
theorem rayleigh_cayley {H T : Type} [Group H] [Group T] [Fintype T] [DecidableEq T]
    (φ : H →* T) (S : Finset H) (hSinv : ∀ s ∈ S, s⁻¹ ∈ S) (hT : 2 ≤ Fintype.card T) :
    IsLeast {r : ℝ | ∃ y : T → ℝ, ∑ t, y t = 0 ∧ y ⬝ᵥ y = 1 ∧
        r = y ⬝ᵥ (laplacian (cayleyMultigraph φ S) *ᵥ y)}
      (lambda1 (laplacian (cayleyMultigraph φ S))) := by sorry

end AlonMilman.PropertyT
