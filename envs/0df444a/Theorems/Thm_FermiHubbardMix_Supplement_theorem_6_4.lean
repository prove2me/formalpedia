-- Prove2me | Theorems.Thm_FermiHubbardMix_Supplement_theorem_6_4
-- name    : FermiHubbardMix.Supplement.theorem_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:05:17.535714+00:00
-- url     : https://prove2.me/theorems/07130e7d-7621-4f31-b9ce-c28d90794c97
-- title:
--   Theorem 6.4 — field-independent qubit Lieb–Robinson bound $\|\cdot\|\le\|O_X\||X|(2\zeta|T|)^\ell/\ell!$
-- statement:
--   Let $H=V+W$ be an $n$-qubit local Hamiltonian with external field, with local interaction strength $\zeta$, and let $H^{\mathrm{int}}_\Omega=V+\sum_{Z_a\subseteq\Omega}h_a$ be its interaction-truncated Hamiltonians. Let $X\subseteq\Omega\subseteq\Lambda\subseteq[n]$ and suppose $\ell=\mathrm{dist}(X,\Lambda\setminus\Omega)\ge2$, the distance being taken in the interaction hypergraph $E_H$. Let $O_X$ be any operator supported on $X$. Then for every $T\in\mathbb R$,
--   $$
--   \Bigl\|e^{iH^{\mathrm{int}}_\Lambda T}\,O_X\,e^{-iH^{\mathrm{int}}_\Lambda T}-e^{iH^{\mathrm{int}}_\Omega T}\,O_X\,e^{-iH^{\mathrm{int}}_\Omega T}\Bigr\|\le\|O_X\|\cdot|X|\cdot\frac{(2\zeta|T|)^\ell}{\ell!}.
--   $$
--   Both evolutions keep every onsite term; the bound does not depend on the size of the external field $V$. It underlies the quasi-locality of the field-resonant Lindbladian's jump operators and coherent terms.
--
--   Differences from the source:
--   - encoding: n-qubit operators; H = V + W with terms h_a of distinct supports Z_a → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ; HamData (Fin n) n with w Z the term of support Z and IsQubitLocal; reason: the same operators and Hamiltonians (the paper combines terms with equal support)
--   - encoding: ℓ = dist(X, Λ ∖ Ω) ≥ 2 (ℓ ∈ ℕ ∪ {∞}) → dist(X, Λ ∖ Ω) = ↑ℓ for a natural number ℓ with 2 ≤ ℓ; reason: the right-hand side (2ζ|T|)^ℓ/ℓ! is undefined at ℓ = ∞; the condition only excludes that undefined case
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Theorem 6.4, p.19

import Mathlib
import Definitions.Def_FermiHubbardMix_Supplement_IsQubitLocal
import Definitions.Def_FermiHubbardMix_HamData
import Definitions.Def_FermiHubbardMix_hgDist
import Definitions.Def_FermiHubbardMix_gibbs
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix.Supplement

/-- **Theorem 6.4 (Field-independent Lieb–Robinson bound)** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…), p.19). Let
`H = V + W` be an `n`-qubit local Hamiltonian with external field (Definition 5.4) with local interaction
strength `ζ`, and `H^int_Ω` the interaction-truncated Hamiltonians (Definition 4.4). Let
`X ⊆ Ω ⊆ Λ ⊆ [n]` with `ℓ = dist(X, Λ ∖ Ω) ≥ 2`, and let `O_X` be supported on `X`. Then for every
`T ∈ ℝ`,
`‖e^{iH^int_Λ T} O_X e^{-iH^int_Λ T} - e^{iH^int_Ω T} O_X e^{-iH^int_Ω T}‖ ≤ ‖O_X‖ · |X| · (2ζ|T|)^ℓ / ℓ!`.

**Formalization Note** `dist` is the hypergraph distance of Definition 4.2 in `E_H` (published
`hgDistSet H.edges`); the bound is meaningful only for finite `ℓ`, encoded as `dist(X, Λ ∖ Ω) = ℓ` for a
natural number `ℓ ≥ 2`. Both evolutions are interaction-truncated and keep every onsite term `v_i`; no
bound on the `v_i` and no `ζ > 0` is assumed. `‖·‖` is the operator norm (`opNorm`), `|X|` the
cardinality of `X`. -/
theorem theorem_6_4 {n : ℕ} (H : HamData (Fin n) n) (hH : IsQubitLocal H)
    (X Ω Λ : Set (Fin n)) (hXΩ : X ⊆ Ω) (hΩΛ : Ω ⊆ Λ) (ℓ : ℕ)
    (hℓ : hgDistSet H.edges X (Λ \ Ω) = ℓ) (h2ℓ : 2 ≤ ℓ) (O : Op n) (hO : IsSuppOn O X) (T : ℝ) :
    opNorm (heis (H.trunc Λ) T O - heis (H.trunc Ω) T O) ≤
      opNorm O * (Nat.card X : ℝ) * (2 * H.zeta * |T|) ^ ℓ / (ℓ.factorial : ℝ) := by sorry

end FermiHubbardMix.Supplement
