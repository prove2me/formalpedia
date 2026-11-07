-- Prove2me | Theorems.Thm_FermiHubbardMix_proposition_12_13
-- name    : FermiHubbardMix.proposition_12_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:34:51.701677+00:00
-- url     : https://prove2.me/theorems/acbfc7ec-b9c7-4c65-bea4-bf3bd19c64fb
-- title:
--   Proposition 12.13 — charging a region: $\operatorname{tr}_S X=0$ gives a transport plan with cost $\le\|X\|_1e_S$
-- statement:
--   Let $X\in\mathfrak A^{\mathrm{ev}}_\Lambda$ be Hermitian, and suppose that $\operatorname{tr}_S(X)=0$ for some $S\subseteq\Lambda$. Then $X$ has a fermionic transport plan $(X_i)_{i\in\Lambda}$ whose cost vector satisfies, entrywise,
--   $$
--   x\le\|X\|_1\,e_S,\qquad\text{i.e.}\quad x_i=\tfrac12\|X_i\|_1\le\|X\|_1\ (i\in S),\qquad x_i=0\ (i\notin S).
--   $$
--   This is the basic charging rule of the transport-plan calculus, used repeatedly in Section 14.
--
--   Differences from the source:
--   - encoding: a fixed ordering of the modes of Λ × [m]; Fock space with operators c_{i,a} → any bijection ord : Λ × Fin m ≃ Fin N; c_k = (γ_{2k} + iγ_{2k+1})/2 from the published Jordan–Wigner Majoranas; reason: the same Fock space and the same CAR operators (proved in the verification files); the paper's results hold for every fixed ordering
--   - encoding: P^i_{µν} = ι_{{i}}(|µ⟩⟨ν|) → c†_µ Π^{{i}}_0 (c†_ν)†; reason: equal up to signs s_µ s_ν ∈ {±1}; the diagonal units coincide and every Lindbladian is quadratic in each jump
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Proposition 12.13, p.56

import Mathlib
import Definitions.Def_FermiHubbardMix_w1
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

/-- **Proposition 12.13 (Charging a region)** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…), p.56). Let `X ∈ 𝔄^ev_Λ` be Hermitian. If
`tr_S(X) = 0` for some `S ⊆ Λ`, then `X` has a fermionic transport plan with cost vector entrywise at
most `‖X‖₁ e_S`.

**Formalization Note** `‖·‖₁` is the trace norm `WildeQIT.traceNorm`; the `i`-th entry of `‖X‖₁ e_S`
is `S.indicator (fun _ => ‖X‖₁) i`. -/
theorem proposition_12_13 {Λ : Type*} [Fintype Λ] {m N : ℕ} (ord : Λ × Fin m ≃ Fin N)
    (X : Op N) (hXh : X.IsHermitian) (hXe : IsEven X) (S : Set Λ) (hS : ptr ord S X = 0) :
    ∃ Xs : Λ → Op N, IsTransportPlan ord X Xs ∧
      ∀ i, planCost Xs i ≤ S.indicator (fun _ => WildeQIT.traceNorm X) i := by sorry

end FermiHubbardMix
