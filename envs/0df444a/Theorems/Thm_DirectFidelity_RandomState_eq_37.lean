-- Prove2me | Theorems.Thm_DirectFidelity_RandomState_eq_37
-- name    : DirectFidelity.RandomState.eq_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:45.466963+00:00
-- url     : https://prove2.me/theorems/809e0f49-638c-477d-b0ea-3bb7518de94c
-- title:
--   (37), p. 7 — Pr[|⟨ψ|W_k|ψ⟩| ≥ τ√(log d)/√d] ≤ 4 exp(−C₁τ²(log d)/η²) with η = 2
-- statement:
--   Let $d = 2^n$, let $W_k \ne I$ be a non-identity $n$-qubit Pauli operator, $\tau = \sqrt{72\pi^3}$ and $C_1 = 2/(9\pi^3)$. If $\psi$ is uniformly distributed on the unit sphere of $\mathbb C^d$, then
--   $$\Pr\Bigl[\,|\langle\psi|W_k|\psi\rangle| \ge \tau\sqrt{\log d}/\sqrt d\,\Bigr] \le 4\exp\!\bigl(-C_1\tau^2(\log d)/\eta^2\bigr),\qquad \eta = 2 .$$
--
--   In the paper this is Levy's lemma applied to the $2$-Lipschitz function of (36), whose mean is $0$. It is the per-label tail bound behind the union bound (38).
--
--   **Formalization Note** $\eta = 2$ is kept visible as $2^2$ in the exponent. For $n = 0$ there is no non-identity label, so that case is empty.
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 7, eq. (37)

import Mathlib
import Definitions.Def_DirectFidelity_RandomState_Setting

namespace DirectFidelity.RandomState

open MeasureTheory

theorem eq_37 (n : ℕ) (k : DirectFidelity.State.P n) (hk : k ≠ (fun _ => 0)) :
    (unifSphere n).real
        {ψ | tau * Real.sqrt (Real.log (DirectFidelity.State.dim n)) / Real.sqrt (DirectFidelity.State.dim n) ≤ ‖pauliExp k (ψ : E n)‖} ≤
      4 * Real.exp (-C1 * tau ^ 2 * Real.log (DirectFidelity.State.dim n) / 2 ^ 2) := by sorry
end DirectFidelity.RandomState
