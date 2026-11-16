-- Prove2me | Theorems.Thm_FermiHubbardMix_Supplement_theorem_8_6
-- name    : FermiHubbardMix.Supplement.theorem_8_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:06:52.105004+00:00
-- url     : https://prove2.me/theorems/e18ccfc7-5e02-4c41-a234-b409cf192ec4
-- title:
--   Theorem 8.6 — qubit rapid mixing with arbitrary external field in time $\lceil 2\log(2n/\varepsilon)\rceil$
-- statement:
--   Let $H=V+W$ act on $n$ qubits, where $W$ is a bounded $L$-local degree-$D$ Hamiltonian and $V=\sum_iv_i$ is an external field with $v_i$ supported on site $i$ only, and let $\sigma=e^{-\beta H}/\mathrm{tr}(e^{-\beta H})$. For every inverse temperature
--   $$
--   \beta\in\bigl(0,\,(DL)^{-3}/28800\bigr]
--   $$
--   and every initial state $\rho$, the field-resonant Lindbladian $\mathcal L_{\mathrm{FR}}$ satisfies
--   $$
--   \bigl\|e^{t\mathcal L_{\mathrm{FR}}}(\rho)-\sigma\bigr\|_1\le\varepsilon
--   $$
--   for every $\varepsilon>0$ and every time $t\ge0$ with $t\ge\lceil2\log(2n/\varepsilon)\rceil$.
--
--   The temperature threshold and the mixing time do not depend on the strength of the external field (formal version of Theorem 1.3).
--
--   **Formalization Note** A state is a positive semidefinite matrix of trace one; $\|\cdot\|_1$ is the trace norm.
--
--   Differences from the source:
--   - encoding: n-qubit operators; H = V + W with terms h_a of distinct supports Z_a → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ; HamData (Fin n) n with w Z the term of support Z and IsQubitLocal; reason: the same operators and Hamiltonians (the paper combines terms with equal support)
--   - reading: outputs a state ρ̂ with ‖ρ̂ − σ‖₁ ≤ ε after running for O(log(2n/ε)) time → ‖e^{tL_FR}(ρ) − σ‖₁ ≤ ε for every t ≥ 0 with t ≥ ⌈2 log(2n/ε)⌉, every ε > 0; reason: the proof (p.40) fixes t_0 = ⌈2 log(2n/ε)⌉ and proves the bound for every t ≥ t_0; a running time is nonnegative
--   - encoding: β ∈ (0, (DL)^{-3}/28800] → 0 < β and 28800 (DL)³ β ≤ 1; reason: the same interval, without division
--   - encoding: initial state ρ → ρ positive semidefinite with trace 1 (FermiCap.Gaussian.IsDensity); reason: the definition of a state
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Theorem 8.6, p.40 (time t_0 = ⌈2 log(2n/ε)⌉ from its proof, p.40); informal Theorem 1.3, p.5

import Mathlib
import Definitions.Def_FermiHubbardMix_Supplement_IsQubitLocal
import Definitions.Def_FermiHubbardMix_Supplement_lindFRQ
import Definitions.Def_FermiHubbardMix_semigroup
import Definitions.Def_FermiHubbardMix_gibbs
import Definitions.Def_FermiCap_Gaussian_States
import Definitions.Def_WildeQIT_traceNorm
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix.Supplement

/-- **Theorem 8.6 (Rapid mixing with arbitrary external field)** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…), p.40; informal
Theorem 1.3, p.5). Let `H = V + W` on `n` qubits, where `W` is a bounded `L`-local degree-`D`
Hamiltonian and `V = ∑_i v_i` is an external field with `v_i` supported on site `i` only, and let
`σ = e^{-βH}/tr(e^{-βH})`. For every `β ∈ (0, (DL)^{-3}/28800]` and every initial state `ρ`, the
field-resonant Lindbladian `L_FR` (Definition 6.3) satisfies `‖e^{tL_FR}(ρ) - σ‖₁ ≤ ε` for every
`ε > 0` and every time `t ≥ 0` with `t ≥ ⌈2 log(2n/ε)⌉`.

**Formalization Note** The printed running time `O(log(2n/ε))` is the time
`t_0 = ⌈2 log(2n/ε)⌉` fixed in the proof (p.40), which shows the bound for every `t ≥ t_0`. The threshold
is `28800 (DL)³ β ≤ 1`. A state is a positive semidefinite matrix of trace one (the published
`FermiCap.Gaussian.IsDensity`, no parity condition); `‖·‖₁` is the trace norm; `e^{tL}` the published
`FermiHubbardMix.semigroup`; `log` is natural. The external field `V` is arbitrary. -/
theorem theorem_8_6 {n : ℕ} (H : HamData (Fin n) n) (hH : IsQubitLocal H) (L D : ℕ)
    (hLD : H.BoundedCouplings L D) (β : ℝ) (hβ : 0 < β) (hβLD : 28800 * ((D : ℝ) * L) ^ 3 * β ≤ 1)
    (ρ : Op n) (hρ : FermiCap.Gaussian.IsDensity ρ) (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht0 : 0 ≤ t)
    (ht : ((⌈2 * Real.log (2 * n / ε)⌉ : ℤ) : ℝ) ≤ t) :
    WildeQIT.traceNorm (semigroup (lindFRQ H β) t ρ - gibbs β H.ham) ≤ ε := by sorry

end FermiHubbardMix.Supplement
