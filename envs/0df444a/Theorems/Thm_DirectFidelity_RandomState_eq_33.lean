-- Prove2me | Theorems.Thm_DirectFidelity_RandomState_eq_33
-- name    : DirectFidelity.RandomState.eq_33
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:36.859728+00:00
-- url     : https://prove2.me/theorems/6fb692ac-ecf0-41ee-a36b-71776884e41b
-- title:
--   (33), p. 7 — ψ ↦ ⟨φ|ψ⟩ is 1-Lipschitz: |⟨φ|ψ⟩ − ⟨φ|ψ′⟩| ≤ ‖ψ − ψ′‖₂
-- statement:
--   Let $\varphi \in \mathbb C^d$ be a state, $\|\varphi\|_2 = 1$. Then for all vectors $\psi, \psi' \in \mathbb C^d$,
--   $$\bigl|\langle\varphi|\psi\rangle - \langle\varphi|\psi'\rangle\bigr| \le \|\psi - \psi'\|_2 .$$
--   That is, the overlap $\psi \mapsto \langle \varphi|\psi\rangle$ is Lipschitz with coefficient $\eta = 1$.
--
--   This is the Lipschitz estimate that feeds Levy's lemma in (34).
--
--   **Formalization Note** The inequality is stated for all vectors $\psi,\psi'$, not only unit vectors; the paper uses it on the unit sphere, so this is a (harmless) generalisation.
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 7, eq. (33)

import Mathlib
import Definitions.Def_DirectFidelity_RandomState_Setting

namespace DirectFidelity.RandomState

open MeasureTheory

theorem eq_33 {n : ℕ} (φ : E n) (hφ : ‖φ‖ = 1) :
    ∀ ψ ψ' : E n, ‖inner ℂ φ ψ - inner ℂ φ ψ'‖ ≤ ‖ψ - ψ'‖ := by sorry
end DirectFidelity.RandomState
