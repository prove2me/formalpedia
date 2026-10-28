-- Prove2me | Theorems.Thm_DirectFidelity_RandomState_lemma_1
-- name    : DirectFidelity.RandomState.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:54.048515+00:00
-- url     : https://prove2.me/theorems/9c1e253d-a695-4660-ac4e-40b8dcfecb56
-- title:
--   Lemma 1, p. 7 — given s ≤ 2^{cd} states there is a state ψ with |⟨φ_i|ψ⟩| ≤ √(9π³(log 2)c) and |⟨ψ|W_k|ψ⟩| ≤ √(72π³)√(log d)/√d for all W_k ≠ I
-- statement:
--   Let $n \ge 1$ qubits, $d = 2^n$, and let $c > 0$. Put
--   $$\varepsilon = \sqrt{9\pi^3(\log 2)\,c},\qquad \tau = \sqrt{72\pi^3}.$$
--   Let $\varphi_1,\dots,\varphi_s \in \mathbb C^d$ be states (unit vectors) with $s \le 2^{cd}$. Then there is a state $\psi \in \mathbb C^d$, $\|\psi\|_2 = 1$, such that
--
--   1. $|\langle\varphi_i|\psi\rangle| \le \varepsilon$ for every $i \in \{1,\dots,s\}$, and
--   2. $|\langle\psi|W_k|\psi\rangle| \le \tau\sqrt{\log d}/\sqrt d$ for every $n$-qubit Pauli operator $W_k \ne I$.
--
--   Applied repeatedly, the lemma produces $2^{\Omega(d)}$ almost-orthogonal states whose Pauli expectation values are all small, the first step of the paper's $\Omega(d^2/\log d)$ lower bound for tomography with Pauli measurements.
--
--   **Formalization Note** The statement adds $n \ge 1$: for $n = 0$ ($d = 1$) and small $c$ it is false, since every unit $\psi\in\mathbb C^1$ has $|\langle\varphi_1|\psi\rangle| = 1 > \varepsilon$. It also takes $c > 0$, the reading of "c is some constant" under which $\varepsilon$ is defined. "$W_k \ne I$" is read as "the label $k$ is not the identity label"; distinct labels give distinct operators. The norm of the complex number $\langle\psi|W_k|\psi\rangle$ is bounded; this number is real since $W_k$ is Hermitian. $\log$ is the natural logarithm.
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 7, Lemma 1, eqs. (31)–(32)

import Mathlib
import Definitions.Def_DirectFidelity_RandomState_Setting

namespace DirectFidelity.RandomState

open MeasureTheory

theorem lemma_1 (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc : 0 < c) (s : ℕ)
    (hs : (s : ℝ) ≤ (2 : ℝ) ^ (c * DirectFidelity.State.dim n)) (φ : Fin s → E n) (hφ : ∀ i, ‖φ i‖ = 1) :
    ∃ ψ : E n, ‖ψ‖ = 1 ∧ (∀ i, ‖inner ℂ (φ i) ψ‖ ≤ epsC c) ∧
      ∀ k : DirectFidelity.State.P n, k ≠ (fun _ => 0) →
        ‖pauliExp k ψ‖ ≤ tau * Real.sqrt (Real.log (DirectFidelity.State.dim n)) / Real.sqrt (DirectFidelity.State.dim n) := by sorry
end DirectFidelity.RandomState
