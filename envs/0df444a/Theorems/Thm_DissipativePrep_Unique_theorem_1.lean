-- Prove2me | Theorems.Thm_DissipativePrep_Unique_theorem_1
-- name    : DissipativePrep.Unique.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:47:05.708301+00:00
-- url     : https://prove2.me/theorems/db911860-3c6d-4d09-b582-b4a4c0ccad71
-- title:
--   Theorem 1, p. 2 — characterization of pure stationary states
-- statement:
--   Let $\mathcal L$ be the Liouvillian of Eq. (2) with Hermitian Hamiltonian $H$, jump operators $c_1,\dots,c_m$ and rates $g_l>0$, and write $P = \sum_l g_l c_l^\dagger c_l$, $Q = P - iH$. Let $|\Phi\rangle$ be a unit vector. Then $\mathcal L(|\Phi\rangle\langle\Phi|) = 0$ if and only if
--
--   1. $Q^\dagger|\Phi\rangle = \lambda|\Phi\rangle$ for some $\lambda\in\mathbb C$, and
--   2. $c_l|\Phi\rangle = \lambda_l|\Phi\rangle$ for every $l$, for some $\lambda_l\in\mathbb C$ with
--   $$\sum_l g_l\,|\lambda_l|^2 = \operatorname{Re}(\lambda).$$
--
--   The theorem reduces stationarity of a pure state to a common-eigenvector condition on the jump operators, which is the basis of the construction in §IV.
--
--   **Formalization Note** The page allows $g_l\ge 0$; with $g_l = 0$ the operator $c_l$ does not enter $\mathcal L$ and condition 2 can fail, so $g_l>0$ is assumed. $|\Phi\rangle$ is required to be a unit vector (a state).
-- source:
--   Kraus et al., Preparation of entangled states by quantum Markov processes, arXiv:0803.1463v3, p. 2, Theorem 1

import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16

namespace DissipativePrep.Unique

theorem theorem_1 {d m : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (c : Fin m → Matrix (Fin d) (Fin d) ℂ) (g : Fin m → ℝ) (hg : ∀ l, 0 < g l)
    (Φ : EuclideanSpace ℂ (Fin d)) (hΦ : ‖Φ‖ = 1) :
    gkslGenerator (krausData H hH c g) (pureDensity Φ) = 0 ↔
      ∃ lam : ℂ, act (Qop H c g)ᴴ Φ = lam • Φ ∧
        ∃ lamL : Fin m → ℂ, (∀ l, act (c l) Φ = lamL l • Φ) ∧
          ∑ l, g l * ‖lamL l‖ ^ 2 = lam.re := by sorry

end DissipativePrep.Unique
