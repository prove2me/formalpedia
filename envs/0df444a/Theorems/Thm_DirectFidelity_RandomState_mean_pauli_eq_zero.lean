-- Prove2me | Theorems.Thm_DirectFidelity_RandomState_mean_pauli_eq_zero
-- name    : DirectFidelity.RandomState.mean_pauli_eq_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:44.197252+00:00
-- url     : https://prove2.me/theorems/7319f410-a58a-4281-b9c3-083259437e69
-- title:
--   p. 7, sentence before (37) — for Haar-random ψ and W_k ≠ I, 𝔼⟨ψ|W_k|ψ⟩ = 0
-- statement:
--   Let $\psi$ be uniformly distributed on the unit sphere of $\mathbb C^d$, $d = 2^n$, and let $W_k \ne I$ be a non-identity $n$-qubit Pauli operator. Then $\psi \mapsto \langle\psi|W_k|\psi\rangle$ is integrable and
--   $$\mathbb E\,\langle\psi|W_k|\psi\rangle = 0 .$$
--
--   This is the centring step ("by symmetry") that lets Levy's lemma be applied around $0$ in (37).
--
--   **Formalization Note** The paper says "for each $k$"; for the identity label the expectation is $1$, so the hypothesis $W_k \ne I$ (the label $k$ is not all zeros) is taken from the context "$\forall W_k \ne I$" of (32), where the claim is used. Integrability is asserted together with the value of the integral.
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 7, sentence before (37)

import Mathlib
import Definitions.Def_DirectFidelity_RandomState_Setting

namespace DirectFidelity.RandomState

open MeasureTheory

theorem mean_pauli_eq_zero (n : ℕ) (k : DirectFidelity.State.P n) (hk : k ≠ (fun _ => 0)) :
    Integrable (fun ψ : Metric.sphere (0 : E n) 1 => pauliExp k (ψ : E n)) (unifSphere n) ∧
      ∫ ψ, pauliExp k (ψ : E n) ∂(unifSphere n) = 0 := by sorry
end DirectFidelity.RandomState
