-- Prove2me | Theorems.Thm_DirectFidelity_RandomState_mean_inner_eq_zero
-- name    : DirectFidelity.RandomState.mean_inner_eq_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:57.513987+00:00
-- url     : https://prove2.me/theorems/9693a37a-a741-463f-9c69-17a1c300375c
-- title:
--   p. 7, sentence before (34) — for Haar-random ψ, 𝔼⟨φ|ψ⟩ = 0
-- statement:
--   Let $\psi$ be uniformly distributed on the unit sphere of $\mathbb C^d$, $d = 2^n$, and let $\varphi \in \mathbb C^d$ be any fixed vector. Then $\psi \mapsto \langle\varphi|\psi\rangle$ is integrable and
--   $$\mathbb E\,\langle \varphi|\psi\rangle = 0 .$$
--
--   This is the centring step ("by symmetry") that lets Levy's lemma be applied around the value $0$ in (34).
--
--   **Formalization Note** The statement asserts integrability together with the value of the integral, so it cannot hold merely because a non-integrable Bochner integral is $0$. It holds for every $\varphi$, unit or not.
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 7, sentence before (34)

import Mathlib
import Definitions.Def_DirectFidelity_RandomState_Setting

namespace DirectFidelity.RandomState

open MeasureTheory

theorem mean_inner_eq_zero (n : ℕ) (φ : E n) :
    Integrable (fun ψ : Metric.sphere (0 : E n) 1 => inner ℂ φ (ψ : E n)) (unifSphere n) ∧
      ∫ ψ, inner ℂ φ (ψ : E n) ∂(unifSphere n) = 0 := by sorry
end DirectFidelity.RandomState
