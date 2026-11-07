-- Prove2me | Theorems.Thm_FermiHubbardMix_proposition_12_18
-- name    : FermiHubbardMix.proposition_12_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:34:51.936193+00:00
-- url     : https://prove2.me/theorems/d2d6ce97-770f-412b-9e25-fbe952cf7265
-- title:
--   Proposition 12.18 — $\tfrac12\|X\|_1\le\|X\|_{W_1}\le n\|X\|_1$, with equality $\tfrac12\|X\|_1$ when $\operatorname{tr}_jX=0$
-- statement:
--   Let $X\in\mathfrak A^{\mathrm{ev}}_\Lambda$ be traceless and Hermitian, and $n=|\Lambda|$. Then
--   $$
--   \tfrac12\|X\|_1\le\|X\|_{W_1}\le n\,\|X\|_1 .
--   $$
--   If moreover $\operatorname{tr}_j(X)=0$ for some site $j$, then $\|X\|_{W_1}=\tfrac12\|X\|_1$.
--
--   The comparison converts Wasserstein contraction into trace-norm mixing at the end of the proof of Theorem 15.1.
--
--   Differences from the source:
--   - encoding: a fixed ordering of the modes of Λ × [m]; Fock space with operators c_{i,a} → any bijection ord : Λ × Fin m ≃ Fin N; c_k = (γ_{2k} + iγ_{2k+1})/2 from the published Jordan–Wigner Majoranas; reason: the same Fock space and the same CAR operators (proved in the verification files); the paper's results hold for every fixed ordering
--   - encoding: P^i_{µν} = ι_{{i}}(|µ⟩⟨ν|) → c†_µ Π^{{i}}_0 (c†_ν)†; reason: equal up to signs s_µ s_ν ∈ {±1}; the diagonal units coincide and every Lindbladian is quadratic in each jump
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Proposition 12.18, p.58

import Mathlib
import Definitions.Def_FermiHubbardMix_w1
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

/-- **Proposition 12.18 (Trace norm versus Wasserstein norm)** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…), p.58). For every traceless
Hermitian `X ∈ 𝔄^ev_Λ`, `½‖X‖₁ ≤ ‖X‖_{W₁} ≤ n‖X‖₁` (`n = |Λ|`); if `tr_j(X) = 0` for some `j ∈ Λ`,
then `‖X‖_{W₁} = ½‖X‖₁`. -/
theorem proposition_12_18 {Λ : Type*} [Fintype Λ] {m N : ℕ} (ord : Λ × Fin m ≃ Fin N)
    (X : Op N) (hXh : X.IsHermitian) (hXe : IsEven X) (hX0 : X.trace = 0) :
    (WildeQIT.traceNorm X / 2 ≤ w1 ord X ∧ w1 ord X ≤ (Fintype.card Λ : ℝ) * WildeQIT.traceNorm X) ∧
      ∀ j : Λ, ptr ord {j} X = 0 → w1 ord X = WildeQIT.traceNorm X / 2 := by sorry

end FermiHubbardMix
