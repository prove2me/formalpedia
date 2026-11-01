-- Prove2me | Theorems.Thm_DualMirrorAlloc_pivot_bound
-- name    : DualMirrorAlloc.pivot_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:03:43.214987+00:00
-- url     : https://prove2.me/theorems/fbf8b8bf-ff2e-4a7e-bce0-c6f723d260fe
-- title:
--   Proof of Theorem 1, Step 3, p.16 — if $\tau_A<T$, the pivot $(\bar f/\rho_j)e_j$ gives $\sum_{t\le\tau_A}w_t\le(\bar f/\rho_j)\bar b-\bar f(T-\tau_A)$
-- statement:
--   Assume the model of §2 and Assumption 1 with constants $\bar f,\bar b\ge0$. Run Algorithm 1 with any selections and any initial point, and let $\tau_A$ be its stopping time. For every request sequence $\vec\gamma$ with $\tau_A<T$ there is a resource $j$ such that
--   $$
--   \sum_{t=1}^{\tau_A}(b_t(x_t))_j+\bar b\ge T\rho_j
--   $$
--   and, for $\mu=(\bar f/\rho_j)e_j$ with $e_j$ the $j$-th unit vector,
--   $$
--   \sum_{t=1}^{\tau_A}w_t(\mu)=\sum_{t=1}^{\tau_A}\mu^\top(\rho-b_t(x_t))\le\frac{\bar f}{\rho_j}\bar b-\bar f(T-\tau_A).
--   $$
--
--   This is the choice of pivot that converts the complementary-slackness bound (11) into the constant $C_1=\bar f\bar b/\underline\rho$ when a resource is nearly exhausted.
--
--   **Formalization Note** Periods are 0-based (sums over indices $t<\tau_A$). $(\bar f/\rho_j)e_j$ is `Pi.single j (fbar / ρ j)`. The statement is pathwise.
--
--   Differences from the source:
--   - encoding: requests γ = (f, b, X) ∈ S → a type S of requests carrying X s, f s, b s (structure Requests); f s, b s typed on all of ℝ^d; reason: values of f, b off X_s are never used
--   - encoding: ‖b(x)‖∞ ≤ b̄ with b(x) ≥ 0; ‖·‖₁ → ∀ j, b_s(x)_j ≤ b̄; ℓ₁ norm as Σ_j |v_j|; reason: Mathlib's norm on Fin m → ℝ is the sup norm; the explicit forms are the paper's norms
--   - encoding: periods t = 1, …, T (sums Σ_{t=1}^{τ}, iterates µ_t) → periods Fin T, 0-based: sums over indices t < τ, and the state at index t is (µ_{t+1}, B_{t+1}); reason: index convention only
--   - reading: τ_A: the first time less than T at which some resource has Σ_{t=1}^{τ_A}(b_t(x_t))_j + b̄ ≥ ρ_jT, else T → the least t ∈ {0, …, T − 1} with that property (sum over the first t periods, empty at t = 0), else T; reason: with the search starting at t = 1 the Step-1 claim fails: m = T = 1, ρ = 1, b̄ = 2, a request with b(x̃₁) = 2 gives x₁ = 0 ≠ x̃₁ while τ_A = 1
--   - generalization: Algorithm 1 under Assumptions 1–2 with step-size η and initial point µ₁ ∈ ℝ^m_+ → any selections act, md and any µ₁; no hypothesis on h, σ or η; reason: the bound uses only the definition of τ_A, ρ > 0 and f̄ ≥ 0; the paper's run is an instance
--   - encoding: (f̄/ρ_j)e_j → Pi.single j (f̄ / ρ j); reason: the j-th unit vector scaled by f̄/ρ_j
-- source:
--   Balseiro–Lu–Mirrokni, The Best of Many Worlds: Dual Mirror Descent for Online Allocation Problems, arXiv:2011.10124v3, proof of Theorem 1, Step 3, p.16

import Mathlib
import Definitions.Def_DualMirrorAlloc_Model

namespace DualMirrorAlloc

/-- **The pivot `µ = (f̄/ρ_j)e_j` when a resource runs low.** Balseiro–Lu–Mirrokni,
arXiv:2011.10124v3, proof of Theorem 1, Step 3, p.16: "If τA < T, then there exists a resource
j ∈ [m] such that Σ_{t=1}^{τA}(bt(xt))j + b̄ ≥ Tρj. Set µ = (f̄/ρj)ej with ej being the j-th unit
vector. This yields Σ_{t=1}^{τA} wt(µ) = Σ_{t=1}^{τA} µᵀ(ρ − bt(xt)) = (f̄/ρj) Σ_{t=1}^{τA}(ρj −
(bt(xt))j) ≤ (f̄/ρj)(τAρj − Tρj + b̄) = (f̄/ρj) b̄ − f̄(T − τA)".

For every request sequence `γ⃗` with `τ_A < T` there is a resource `j` with
`Σ_{t=1}^{τ_A} (b_t(x_t))_j + b̄ ≥ Tρ_j` and, for that `j`,
`Σ_{t=1}^{τ_A} w_t((f̄/ρ_j)e_j) ≤ (f̄/ρ_j) b̄ − f̄(T − τ_A)`.

**Formalization Note.** Time is 0-based: `Σ_{t=1}^{τ_A}` is the sum over indices `t < τ_A`
(`consumed … τ_A` for the consumption). `(f̄/ρ_j)e_j` is `Pi.single j (f̄ / ρ j)`. The statement
holds for every selection `act`, `md` and every `µ_1`: it uses only the definition of `τ_A`,
`ρ > 0` and `f̄ ≥ 0`. -/
theorem pivot_bound {S : Type*} {d m : ℕ}
    (R : Requests S d m) (ρ : Fin m → ℝ) (hmodel : IsModel R ρ)
    (fbar bbar : ℝ) (hA1 : Assumption1 R fbar bbar)
    (act : S → (Fin m → ℝ) → (Fin d → ℝ)) (md : (Fin m → ℝ) → (Fin m → ℝ) → (Fin m → ℝ))
    (mu₁ : Fin m → ℝ) (T : ℕ) (γ : Fin T → S)
    (hτ : tauA R ρ act md mu₁ bbar γ < T) :
    ∃ j, ρ j * T ≤ consumed R ρ act md mu₁ γ (tauA R ρ act md mu₁ bbar γ) j + bbar ∧
      ∑ t : Fin T with t.val < tauA R ρ act md mu₁ bbar γ,
          wFn R ρ act md mu₁ γ t (Pi.single j (fbar / ρ j)) ≤
        fbar / ρ j * bbar - fbar * (T - (tauA R ρ act md mu₁ bbar γ : ℝ)) := by sorry

end DualMirrorAlloc
