-- Prove2me | Theorems.Thm_FermiHubbardMix_theorem_13_5
-- name    : FermiHubbardMix.theorem_13_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:35:29.950606+00:00
-- url     : https://prove2.me/theorems/73c512aa-d9c9-4981-b618-5a55d7c5d3aa
-- title:
--   Theorem 13.5 — field-independent fermionic Lieb–Robinson bound $\|\cdot\|\le\|A\||X|(2\zeta|T|)^\ell/\ell!$
-- statement:
--   Let $H=V+W$ be a local fermionic Hamiltonian with onsite terms on $\Lambda$, with local multi-site coupling strength $\zeta>0$. Let $X\subseteq\Omega\subseteq\Lambda$ and $\ell=\mathrm{dist}(X,\Lambda\setminus\Omega)$ in the hypergraph $E_H$. If $2\le\ell<\infty$, then for every $T\in\mathbb R$ and every $A\in\mathfrak A_X$,
--   $$
--   \bigl\|e^{iTH}Ae^{-iTH}-e^{iTH^{\mathrm{int}}_\Omega}Ae^{-iTH^{\mathrm{int}}_\Omega}\bigr\|\le\|A\|\cdot|X|\cdot\frac{(2\zeta|T|)^\ell}{\ell!}.\tag{20}
--   $$
--   The constants do not depend on the onsite terms $v_i$; this is what makes the later quasi-locality estimates field-independent.
--
--   Differences from the source:
--   - encoding: a fixed ordering of the modes of Λ × [m]; Fock space with operators c_{i,a} → any bijection ord : Λ × Fin m ≃ Fin N; c_k = (γ_{2k} + iγ_{2k+1})/2 from the published Jordan–Wigner Majoranas; reason: the same Fock space and the same CAR operators (proved in the verification files); the paper's results hold for every fixed ordering
--   - encoding: 2 ≤ ℓ < ∞ → dist(X, Ωᶜ) = ↑ℓ for a natural number ℓ with 2 ≤ ℓ; reason: the same condition in ℕ∞
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Theorem 13.5, p.61, eq. (20)

import Mathlib
import Definitions.Def_FermiHubbardMix_HamData
import Definitions.Def_FermiHubbardMix_hgDist
import Definitions.Def_FermiHubbardMix_gibbs
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

/-- **Theorem 13.5 (Field-independent fermionic Lieb–Robinson bound)** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…), p.61). Let `H = V + W`
be a local fermionic Hamiltonian with onsite terms with local multi-site coupling strength `ζ > 0`.
Let `X ⊆ Ω ⊆ Λ` and `ℓ = dist(X, Λ ∖ Ω)` (in the hypergraph `E_H`). If `2 ≤ ℓ < ∞`, then for every
`T ∈ ℝ` and every `A ∈ 𝔄_X`,
`‖e^{iTH} A e^{-iTH} - e^{iTH^int_Ω} A e^{-iTH^int_Ω}‖ ≤ ‖A‖ |X| (2ζ|T|)^ℓ / ℓ!`  (eq. (20)).

**Formalization Note** `ℓ < ∞` is encoded by `dist(X, Ωᶜ) = ℓ` for a natural number `ℓ`. -/
theorem theorem_13_5 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {m N : ℕ} (ord : Λ × Fin m ≃ Fin N)
    (H : HamData Λ N) (hH : H.IsLocal ord) (hζ : 0 < H.zeta) (X Ω : Set Λ) (hXΩ : X ⊆ Ω)
    (ℓ : ℕ) (hℓ : hgDistSet H.edges X Ωᶜ = ℓ) (h2ℓ : 2 ≤ ℓ) (T : ℝ) (A : Op N)
    (hA : A ∈ localAlg ord X) :
    opNorm (heis H.ham T A - heis (H.trunc Ω) T A) ≤
      opNorm A * (Nat.card X : ℝ) * (2 * H.zeta * |T|) ^ ℓ / (ℓ.factorial : ℝ) := by sorry

end FermiHubbardMix
