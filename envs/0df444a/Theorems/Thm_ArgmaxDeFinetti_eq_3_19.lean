-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_eq_3_19
-- name    : ArgmaxDeFinetti.eq_3_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:43:05.023057+00:00
-- url     : https://prove2.me/theorems/503af6e1-0fa5-4c33-b5f5-bb4801ad691e
-- title:
--   Eq. (3.19) — $\lambda c=\langle u^{\otimes N},M^{[N]}\psi\rangle=\langle u^{\otimes N},M_{12}\psi\rangle=\langle Mu^{\otimes2},\eta_u\rangle$
-- statement:
--   Let $N=2+m$, $d\ge2$, and $M\in\mathrm{Herm}(\mathrm{Sym}^2(\mathbb C^d))$.
--
--   1. There is a unit top eigenvector $\psi\in\mathrm{Sym}^N$ of $M^{[N]}$: $M^{[N]}\psi=\lambda_{\max}(M^{[N]})\,\psi$.
--   2. For every symmetric $\psi\in\mathrm{Sym}^N$ and every $u\in\mathbb C^d$,
--   $$
--   \langle u^{\otimes N},M^{[N]}\psi\rangle=\langle u^{\otimes N},M_{12}\psi\rangle=\langle Mu^{\otimes2},\eta_u\rangle ,
--   $$
--   where $M_{12}$ acts as $M$ on sites $1,2$ and $\eta_u=(\langle u|^{\otimes(N-2)}\otimes I)\psi$.
--   3. If moreover $M^{[N]}\psi=\lambda\psi$, then $\lambda c=\langle u^{\otimes N},M^{[N]}\psi\rangle$ with $c=\langle u^{\otimes N},\psi\rangle$.
--
--   Applied to the argmax rounding object $u$ of a unit top eigenvector $\psi$, this is (3.19), the identity that starts the proof of Proposition 3.5.
--
--   Differences from the source:
--   - encoding: N ≥ 2 → N = 2 + m with m : ℕ; reason: the same values of N
--   - encoding: M ∈ Herm(Sym²(H)) → a Hermitian matrix on ℂ^d ⊗ ℂ^d with U_π M = M U_π = M for π ∈ S₂ (IsSymWitness); reason: extension by zero of the operator on Sym²; it has the same operator norm, a_M, h(M), lift and τ(M)
--   - encoding: λ_max(M^[N]) of M^[N] on Sym^N(H) → supremum of Re⟨ψ, M^[N]ψ⟩ over unit ψ ∈ Sym^N (lamMaxSym); reason: the top eigenvalue of a Hermitian operator on Sym^N is its largest Rayleigh quotient
--   - generalization: u the argmax rounding object of ψ, ψ a unit top eigenvector → the two equalities for every u ∈ ℂ^d and every symmetric ψ; λc = ⟨u^⊗N, M^[N]ψ⟩ for every eigenpair (λ, ψ); reason: the page justifies them by symmetry of u^⊗N and ψ only; the statement specializes to the page's u and ψ
--   - encoding: "Let ψ ∈ Sym^N(H) be a unit top eigenvector of M^[N], with eigenvalue λ" → existence of a unit symmetric ψ with M^[N]ψ = λ_max(M^[N])ψ; reason: the premise the step relies on, stated as a clause
--   - encoding: M_12 on sites 1, 2; η_u contracting N − 2 sites → siteOp M 0 1 (0-based sites) and etaU keeping sites 1, 2; reason: the same two sites in both; 0-based indexing
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), proof of Proposition 3.5, p.26, eq. (3.19)

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_vnorm
import Definitions.Def_ArgmaxDeFinetti_IsSym
import Definitions.Def_ArgmaxDeFinetti_liftN
import Definitions.Def_ArgmaxDeFinetti_IsSymWitness
import Definitions.Def_ArgmaxDeFinetti_lamMaxSym
import Definitions.Def_ArgmaxDeFinetti_etaU

open Matrix
open scoped ComplexOrder

namespace ArgmaxDeFinetti

/-- **Eq. (3.19)**, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), proof of Proposition 3.5, p.26. Let `M ∈ Herm(Sym²(ℂ^d))` and `N, d ≥ 2`. A unit top
eigenvector `ψ ∈ Sym^N` of `M^{[N]}` exists, with eigenvalue `λ_max(M^{[N]})`; and since `u^{⊗N}` and `ψ` are
symmetric, `λc = ⟨u^{⊗N}, M^{[N]}ψ⟩ = ⟨u^{⊗N}, M₁₂ψ⟩ = ⟨M u^{⊗2}, η_u⟩`, with `c = ⟨u^{⊗N}, ψ⟩`.

**Formalization Note** `N = 2 + m`. The two equalities `⟨u^{⊗N}, M^{[N]}ψ⟩ = ⟨u^{⊗N}, M₁₂ψ⟩ = ⟨M u^{⊗2}, η_u⟩` are
stated for every symmetric `ψ` and every `u` (the page's justification uses only symmetry), and `λc = ⟨u^{⊗N},
M^{[N]}ψ⟩` for every eigenvalue `λ` of `ψ`. `M₁₂` is `siteOp M 0 1` (sites `1, 2`, 0-based `0, 1`), matching the two
sites `η_u` keeps (`etaU`). The existence clause is the premise "let `ψ` be a unit top eigenvector" of the page. -/
theorem eq_3_19 (m d : ℕ) (hd : 2 ≤ d) (M : Op 2 d) (hMw : IsSymWitness M) :
    (∀ ψ : Vec (2 + m) d, IsSym ψ → ∀ u : Fin d → ℂ,
      vinner (tensorPow u (2 + m)) (liftN (2 + m) M *ᵥ ψ) =
          vinner (tensorPow u (2 + m)) (siteOp M ⟨0, by omega⟩ ⟨1, by omega⟩ *ᵥ ψ) ∧
      vinner (tensorPow u (2 + m)) (siteOp M ⟨0, by omega⟩ ⟨1, by omega⟩ *ᵥ ψ) =
          vinner (M *ᵥ tensorPow u 2) (etaU u ψ) ∧
      ∀ lam : ℂ, liftN (2 + m) M *ᵥ ψ = lam • ψ →
        lam * vinner (tensorPow u (2 + m)) ψ = vinner (tensorPow u (2 + m)) (liftN (2 + m) M *ᵥ ψ)) ∧
    ∃ ψ : Vec (2 + m) d, IsSym ψ ∧ vnorm ψ = 1 ∧
      liftN (2 + m) M *ᵥ ψ = ((lamMaxSym (2 + m) M : ℝ) : ℂ) • ψ := by sorry

end ArgmaxDeFinetti
