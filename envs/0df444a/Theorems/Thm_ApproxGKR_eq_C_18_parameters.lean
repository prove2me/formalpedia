-- Prove2me | Theorems.Thm_ApproxGKR_eq_C_18_parameters
-- name    : ApproxGKR.eq_C_18_parameters
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:55.992313+00:00
-- url     : https://prove2.me/theorems/2fd88caf-eb91-468f-9688-c1961c77db85
-- title:
--   (C.17)–(C.18) — the choice of $N$, $\alpha$, $\beta$ and $\Delta_0$
-- statement:
--   Let the circuit shape satisfy $L\ge1$, $m_0=0$, $m_i\ge1$ ($1\le i\le L$), $h=2^t\ge2$; let $\delta\ge0$, $K\ge0$, $0<\varepsilon<1$ and $\Delta>0$. With $D=\delta+h-1$, $\vartheta=\varepsilon/(4(kD+L))$, $\alpha=\vartheta^D$, $\beta=\vartheta$, $N$ the least power of two at least $1/\vartheta$, $\Gamma=6(5(1+K)/\beta)^L(9h/\alpha)^k$ and $\Delta_0=2^{-\max\{0,\lceil\log_2(\Gamma/\Delta)\rceil\}}$:
--   1. $kD(\alpha^{1/D}+N^{-1})+L(\beta+N^{-1})\le\varepsilon/2$;
--   2. $h\le D+1\le kD$ and $N>4kD$;
--   3. $\Omega_h\subseteq\Omega_N$, and $\Omega_J\subseteq\Omega_N$ for every power of two $J\le2(D+1)$;
--   4. $0<\Delta_0\le1$ and $E_0\le\Delta_0\Gamma\le\Delta$, with $E_0$ of (C.14)–(C.15) at these $K,\alpha,\beta,\Delta_0$.
--
--   These are the choices of $N$ and $\Delta_0$ in Theorem C.1: soundness error at most $\varepsilon/2$ and every output error above $\Delta$ covered by the soundness argument.
--
--   Differences from the source:
--   - generalization: K of (C.7) → any K ≥ 0; reason: the inequalities use only K ≥ 0
--   - generalization: the Fourier grid of (C.8) (one power of two J ≤ 2(D + 1)) → every power of two J ≤ 2(D + 1); reason: the page's J is one of them
--   - generalization: rational ε and ∆ → real ε and ∆; reason: the rationals are reals
--   - generalization: the conclusions of p.39 → also 0 < ∆₀ ≤ 1; reason: immediate from (C.18); Theorem C.1 requires it
--   - encoding: the least power of two at least 1/ϑ; log → 2^{⌈log₂⌈1/ϑ⌉⌉}; log₂; reason: the same number; p.5: logarithms use base two
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §C.3, eqs. (C.17)–(C.18), p.39

import Mathlib
import Definitions.Def_ApproxGKR_root
import Definitions.Def_ApproxGKR_LayeredCircuit
import Definitions.Def_ApproxGKR_E0
import Definitions.Def_ApproxGKR_Delta0

namespace ApproxGKR

/-- **Equations (C.17)–(C.18): the choice of `N`, `α`, `β` and `∆₀`** (p.39).

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), §C.3, p.39: "First set `ϑ = ε/(4(kD + L))`, `α = ϑ^D`, `β = ϑ`, (C.17) and take
`N` to be the least power of two at least `1/ϑ`. The bound in Equation (C.16) is then at most
`ε/2`. Moreover, `h ≤ D + 1 ≤ kD` and `N > 4kD`, so both `H` and the Fourier grid in
Equation (C.8) are subsets of `ΩN`." "`Γ = 6(5(1 + K)/β)^L (9h/α)^k`,
`∆0 = 2^{−max{0,⌈log(Γ/∆)⌉}}`. (C.18) These choices give `E0 ≤ ∆0Γ ≤ ∆`."

For every circuit shape (`L ≥ 1`, `m₀ = 0`, `mᵢ ≥ 1`, `h = 2^t ≥ 2`), `δ ≥ 0`, `K ≥ 0`,
`0 < ε < 1` and `∆ > 0`:
1. (C.16) at these `α`, `β`, `N` is at most `ε/2`;
2. `h ≤ D + 1 ≤ kD` and `N > 4kD`;
3. `Ω_h ⊆ Ω_N`, and `Ω_J ⊆ Ω_N` for every power of two `J ≤ 2(D + 1)`;
4. `0 < ∆₀ ≤ 1`, and `E₀ ≤ ∆₀Γ ≤ ∆` with `E₀` of (C.14)–(C.15) at `K`, `α`, `β`, `∆₀`.

**Formalization Note** `log` is `log₂`; `N = 2^{⌈log₂⌈1/ϑ⌉⌉}` is the least power of two at least
`1/ϑ`. `K ≥ 0` is arbitrary (the page uses `K` of (C.7)). -/
theorem eq_C_18_parameters (C : LayeredCircuit) (δ : ℕ) (K ε Δ : ℝ) (hK : 0 ≤ K)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hΔ : 0 < Δ) :
    let D := C.Dpar δ
    let θ := theta ε C.k D C.L
    let α := θ ^ D
    let β := θ
    let N := Npar θ
    let Γ := Gamma C.L C.k C.h K α β
    let Δ₀ := Delta0 Γ Δ
    (C.k : ℝ) * D * (α ^ ((1 : ℝ) / D) + 1 / N) + C.L * (β + 1 / N) ≤ ε / 2 ∧
    C.h ≤ D + 1 ∧ D + 1 ≤ C.k * D ∧ 4 * C.k * D < N ∧
    Omega C.h ⊆ Omega N ∧ (∀ J s : ℕ, J = 2 ^ s → J ≤ 2 * (D + 1) → Omega J ⊆ Omega N) ∧
    0 < Δ₀ ∧ Δ₀ ≤ 1 ∧ E0 C K α β Δ₀ ≤ Δ₀ * Γ ∧ Δ₀ * Γ ≤ Δ := by sorry

end ApproxGKR
