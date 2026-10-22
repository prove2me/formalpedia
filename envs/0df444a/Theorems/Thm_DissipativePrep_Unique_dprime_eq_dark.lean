-- Prove2me | Theorems.Thm_DissipativePrep_Unique_dprime_eq_dark
-- name    : DissipativePrep.Unique.dprime_eq_dark
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:47:14.986997+00:00
-- url     : https://prove2.me/theorems/68ba5d95-b83e-427c-9e08-ed32de3054e6
-- title:
--   p. 3 and footnote [35] — D′ = D: Q†ψ = iλψ with λ real iff ψ is dark
-- statement:
--   Let $H$ be Hermitian, $c_1,\dots,c_m$ jump operators with rates $g_l>0$, $P = \sum_l g_l c_l^\dagger c_l$ and $Q = P - iH$. Then
--   $$D' = \{\psi : Q^\dagger\psi = i\lambda\psi \text{ for some } \lambda\in\mathbb R\} \;=\; \{\psi : c_l\psi = 0 \text{ for all } l, \text{ and } H\psi = E\psi \text{ for some } E\in\mathbb R\} = D.$$
--
--   The right-hand side is the paper's set $D = K(P)\cap ES(H)$ of dark vectors (the union over the eigenvalues $E$ of $H$; the zero vector belongs to both sides). The identity is used in the proof of Theorem 2 to show that a stationary state maps $D$ into itself.
--
--   **Formalization Note** $g_l>0$ is assumed so that $K(P)$ is the common kernel of the $c_l$.
-- source:
--   Kraus et al., Preparation of entangled states by quantum Markov processes, arXiv:0803.1463v3, p. 3 (proof of Theorem 2), with footnote [35], p. 10

import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16

namespace DissipativePrep.Unique

theorem dprime_eq_dark {d m : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (c : Fin m → Matrix (Fin d) (Fin d) ℂ) (g : Fin m → ℝ) (hg : ∀ l, 0 < g l) :
    {ψ : EuclideanSpace ℂ (Fin d) | ∃ lam : ℝ, act (Qop H c g)ᴴ ψ = (Complex.I * lam) • ψ} =
      {ψ | (∀ l, act (c l) ψ = 0) ∧ ∃ E : ℝ, act H ψ = (E : ℂ) • ψ} := by sorry

end DissipativePrep.Unique
