-- Prove2me | Theorems.Thm_FermiHubbardMix_Supplement_theorem_7_3
-- name    : FermiHubbardMix.Supplement.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:06:04.809221+00:00
-- url     : https://prove2.me/theorems/73a58649-c5d0-4be9-add3-f4a9125353b1
-- title:
--   Theorem 7.3 — update matrix $(1+c_i\delta^2)I+\delta Q^{(i)}$ of $\mathcal I+\delta\mathcal L_{\mathrm{FR},i}$ for qubits
-- statement:
--   Let $H=V+W$ be an $n$-qubit local Hamiltonian with external field, with local interaction strength $\zeta$, and assume $0<\beta\le 1/(12\zeta)$. For each $i\in[n]$ and every $\delta\in[0,1/(6\sqrt2)]$, the map $\Phi_i=\mathcal I+\delta\mathcal L_{\mathrm{FR},i}$ has the update matrix
--   $$
--   (1+c_i\delta^2)\,I+\delta\,Q^{(i)},\qquad Q^{(i)}=-\frac{e^{-1/4}}{\sqrt2}E_{\{i\}}+120\sum_{r\ge1}(6\beta\zeta)^r\,E_{\mathfrak B(\{i\},r)},
--   $$
--   where $c_i=144+324\bigl(\log(2\sqrt{\Delta_i\beta})+4\bigr)^2$, $\Delta_i=\max(1/\beta,\lambda_{\max}(v_i)-\lambda_{\min}(v_i))$, $E_S=e_Se_S^{\mathsf T}$, $\mathfrak B(\{i\},r)$ is the ball of radius $r$ around $i$ in the interaction hypergraph, $I$ is the $n\times n$ identity matrix and $\log$ is the natural logarithm.
--
--   The negative diagonal term is the local contraction at site $i$; the tail measures leakage to larger balls. Summed over sites, these update matrices give the Dobrushin-type contraction behind Theorem 8.6.
--
--   Differences from the source:
--   - encoding: n-qubit operators; H = V + W with terms h_a of distinct supports Z_a → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ; HamData (Fin n) n with w Z the term of support Z and IsQubitLocal; reason: the same operators and Hamiltonians (the paper combines terms with equal support)
--   - encoding: 0 < β ≤ 1/(12ζ) → 0 < β and 12βζ ≤ 1; reason: the same condition for ζ > 0; at ζ = 0 both allow every β > 0
--   - encoding: Φ_i has an update matrix Q (Definition 7.2, for a trace-preserving map taking Hermitian to Hermitian matrices) → IsQUpdateMatrix Φ_i Q, which asserts that Φ_i preserves Hermiticity and the trace together with the cost condition; reason: Definition 7.2 presupposes this property of Φ (§4's convention for maps); it holds for I + δL_FR,i
--   - encoding: ∑_{r≥1} (6βζ)^r E_{𝔅({i},r)} → tsum over r : ℕ of (6βζ)^(r+1) • blockOnes (hgBall H.edges {i} (r+1)); reason: the same convergent series (6βζ ≤ 1/2)
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Theorem 7.3, p.27

import Mathlib
import Definitions.Def_FermiHubbardMix_Supplement_IsQubitLocal
import Definitions.Def_FermiHubbardMix_Supplement_lindFRQ
import Definitions.Def_FermiHubbardMix_Supplement_IsQUpdateMatrix
import Definitions.Def_FermiHubbardMix_w1
import Definitions.Def_FermiHubbardMix_hgDist
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix.Supplement

/-- **Theorem 7.3 (Update matrix of the Lindbladian evolution at a site)** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…), p.27).
Let `H = V + W` be an `n`-qubit local Hamiltonian with external field (Definition 5.4) with local
interaction strength `ζ`, and assume `0 < β ≤ 1/(12ζ)`. For each `i ∈ [n]` and every
`δ ∈ [0, 1/(6√2)]`, `Φ_i = ℐ + δ L_FR,i` (Definition 6.3) has the update matrix
`(1 + c_i δ²) I + δ Q^{(i)}`, where
`Q^{(i)} = -(e^{-1/4}/√2) E_{{i}} + 120 ∑_{r ≥ 1} (6βζ)^r E_{𝔅({i},r)}` and
`c_i = 144 + 324 (log(2√(Δ_i β)) + 4)²`.

**Formalization Note** `E_S = e_S e_Sᵀ` is the published `blockOnes S` and `𝔅({i}, r)` the published
`hgBall H.edges {i} r`; the series over `r ≥ 1` is a `tsum` indexed by `r + 1` (it converges since
`6βζ ≤ 1/2`). `β ≤ 1/(12ζ)` is written `12βζ ≤ 1` (no division, so `ζ = 0` is allowed) and
`δ ≤ 1/(6√2)` as `6√2 δ ≤ 1`. `I` is the `n × n` identity matrix; `log` is the natural logarithm;
`Δ_i = max(1/β, λ_max(v_i) - λ_min(v_i))` is `deltaQ H β i`. -/
theorem theorem_7_3 {n : ℕ} (H : HamData (Fin n) n) (hH : IsQubitLocal H) (β : ℝ) (hβ : 0 < β)
    (hβζ : 12 * β * H.zeta ≤ 1) (i : Fin n) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : 6 * Real.sqrt 2 * δ ≤ 1) :
    IsQUpdateMatrix (LinearMap.id + (δ : ℂ) • lindFRQSite H β i)
      ((1 + (144 + 324 * (Real.log (2 * Real.sqrt (deltaQ H β i * β)) + 4) ^ 2) * δ ^ 2) •
          (1 : Matrix (Fin n) (Fin n) ℝ) +
        δ • (-((Real.exp (-(1 / 4)) / Real.sqrt 2) • blockOnes ({i} : Set (Fin n))) +
          (120 : ℝ) • ∑' r : ℕ,
            (6 * β * H.zeta) ^ (r + 1) • blockOnes (hgBall H.edges {i} (r + 1)))) := by sorry

end FermiHubbardMix.Supplement
