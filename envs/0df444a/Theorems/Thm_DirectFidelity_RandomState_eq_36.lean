-- Prove2me | Theorems.Thm_DirectFidelity_RandomState_eq_36
-- name    : DirectFidelity.RandomState.eq_36
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:39.864002+00:00
-- url     : https://prove2.me/theorems/0f714eca-581c-4994-bf65-25ca07a71bde
-- title:
--   (36), p. 7 — on unit vectors ψ ↦ ⟨ψ|W_k|ψ⟩ is 2-Lipschitz
-- statement:
--   Let $W_k$ be an $n$-qubit Pauli operator and let $\psi, \psi' \in \mathbb C^d$ be unit vectors. Then
--   $$\bigl|\langle\psi|W_k|\psi\rangle - \langle\psi'|W_k|\psi'\rangle\bigr| \le \bigl|\langle\psi|W_k\bigl[|\psi\rangle - |\psi'\rangle\bigr]\bigr| + \bigl|\bigl[\langle\psi| - \langle\psi'|\bigr]W_k|\psi'\rangle\bigr| \le 2\|\psi - \psi'\|_2 .$$
--   So on the unit sphere the Pauli expectation is Lipschitz with coefficient $\eta = 2$.
--
--   This is the Lipschitz estimate that feeds Levy's lemma in (37).
--
--   **Formalization Note** Both inequalities of the printed chain are stated. The unit-norm hypotheses on $\psi, \psi'$ are the paper's (they are points of the sphere) and are needed, since the map is quadratic.
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 7, eq. (36)

import Mathlib
import Definitions.Def_DirectFidelity_RandomState_Setting

namespace DirectFidelity.RandomState

open MeasureTheory

theorem eq_36 {n : ℕ} (k : DirectFidelity.State.P n) (ψ ψ' : E n) (hψ : ‖ψ‖ = 1) (hψ' : ‖ψ'‖ = 1) :
    ‖pauliExp k ψ - pauliExp k ψ'‖ ≤
        ‖inner ℂ ψ (Matrix.toEuclideanLin (DirectFidelity.State.W k) (ψ - ψ'))‖ +
          ‖inner ℂ (ψ - ψ') (Matrix.toEuclideanLin (DirectFidelity.State.W k) ψ')‖ ∧
      ‖inner ℂ ψ (Matrix.toEuclideanLin (DirectFidelity.State.W k) (ψ - ψ'))‖ +
          ‖inner ℂ (ψ - ψ') (Matrix.toEuclideanLin (DirectFidelity.State.W k) ψ')‖ ≤ 2 * ‖ψ - ψ'‖ := by sorry
end DirectFidelity.RandomState
