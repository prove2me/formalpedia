-- Prove2me | Theorems.Thm_DissipativePrep_Unique_dark_stationary
-- name    : DissipativePrep.Unique.dark_stationary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:47:07.907348+00:00
-- url     : https://prove2.me/theorems/74b8050f-2f54-49cf-85ba-3cc12a33afc1
-- title:
--   §II, p. 2 — dark states are stationary
-- statement:
--   Let $H$ be a Hermitian $d\times d$ matrix, $c_1,\dots,c_m$ jump operators with rates $g_l>0$, and $\mathcal L = \mathcal L_{H,c_l}$ the Liouvillian of Eq. (2). Fix a real number $E$ and let $D_E = K(P)\cap\ker(H-E)$ be the dark space (vectors annihilated by every $c_l$ and with $H$-eigenvalue $E$). Then:
--
--   1. for every $\psi\in D_E$,
--   $$\mathcal L\bigl(|\psi\rangle\langle\psi|\bigr) = 0;$$
--   2. every density matrix $\rho$ whose range $R(\rho)$ is contained in $D_E$ is a stationary state: $\rho \succeq 0$, $\operatorname{tr}\rho = 1$ and $\mathcal L(\rho) = 0$.
--
--   These are the stationary states the paper calls dark states; Theorem 2 gives a condition under which there are no others.
--
--   **Formalization Note** The page's $D = K(P)\cap ES(H)$ is taken with one fixed eigenvalue $E$ of $H$ (the page assumes on p. 3 that $D$ is a subspace, i.e. all dark states share one eigenvalue). Part 1 holds for every $E$, hence for every dark vector. Rates $g_l>0$ are assumed throughout the mission (the page allows $g_l\ge 0$ on p. 1); $|\psi\rangle\langle\psi|$ is unnormalized.
-- source:
--   Kraus et al., Preparation of entangled states by quantum Markov processes, arXiv:0803.1463v3, p. 2, §II ("Thus, if |Ψ⟩ ∈ D_{H,c_l} …")

import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16

namespace DissipativePrep.Unique

theorem dark_stationary {d m : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (c : Fin m → Matrix (Fin d) (Fin d) ℂ) (g : Fin m → ℝ) (hg : ∀ l, 0 < g l) (E : ℝ) :
    (∀ ψ ∈ darkSpace H c E, gkslGenerator (krausData H hH c g) (pureDensity ψ) = 0) ∧
    ∀ ρ : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix ρ → densitySupport ρ ≤ darkSpace H c E →
      stationary (krausData H hH c g) ρ := by sorry

end DissipativePrep.Unique
