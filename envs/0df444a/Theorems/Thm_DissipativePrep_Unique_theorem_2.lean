-- Prove2me | Theorems.Thm_DissipativePrep_Unique_theorem_2
-- name    : DissipativePrep.Unique.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:47:07.998078+00:00
-- url     : https://prove2.me/theorems/2da459ea-98f6-4fbc-b281-d5af81dc48d5
-- title:
--   Theorem 2, p. 3 — no nonzero jump-invariant subspace orthogonal to D ⇒ the only stationary states are the dark states
-- statement:
--   Let $\mathcal L$ be the Liouvillian of Eq. (2) with Hermitian $H$, jump operators $c_1,\dots,c_m$ and rates $g_l>0$. Fix a real number $E$ and assume that $D$ is a subspace in the sense of p. 3: every nonzero dark vector (annihilated by all $c_l$ and an eigenvector of $H$) has $H$-eigenvalue $E$, so $D = D_E = K(P)\cap\ker(H-E)$. Suppose that there is no nonzero subspace $S$ with
--   $$S\perp D \quad\text{and}\quad c_l S\subseteq S \text{ for all } l.$$
--   Then every stationary state is a dark state: if $\rho$ is a density matrix with $\mathcal L(\rho) = 0$, then $R(\rho)\subseteq D$.
--
--   Together with the converse (dark states are stationary, §II) this characterizes all stationary states, and it is the uniqueness criterion applied in §IV.
--
--   **Formalization Note** The page quantifies over all subspaces $S$; the zero subspace is always invariant and orthogonal to $D$, so the printed hypothesis would never hold, and the Lean statement quantifies over nonzero $S$ (P16's `lazy`). Rates $g_l>0$ are assumed. The standing assumption "all the states in $D$ correspond to the same eigenvalue of the Hamiltonian" is kept as a hypothesis.
-- source:
--   Kraus et al., Preparation of entangled states by quantum Markov processes, arXiv:0803.1463v3, p. 3, Theorem 2 (with the standing assumption stated just before it)

import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16

namespace DissipativePrep.Unique

theorem theorem_2 {d m : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (c : Fin m → Matrix (Fin d) (Fin d) ℂ) (g : Fin m → ℝ) (hg : ∀ l, 0 < g l) (E : ℝ)
    (hD : ∀ (ψ : EuclideanSpace ℂ (Fin d)) (E' : ℝ), ψ ≠ 0 → (∀ l, act (c l) ψ = 0) →
      act H ψ = (E' : ℂ) • ψ → E' = E)
    (hS : ∀ S : Submodule ℂ (EuclideanSpace ℂ (Fin d)), lazy c S → ¬ S ≤ (darkSpace H c E)ᗮ) :
    ∀ ρ : Matrix (Fin d) (Fin d) ℂ, stationary (krausData H hH c g) ρ →
      densitySupport ρ ≤ darkSpace H c E := by sorry

end DissipativePrep.Unique
