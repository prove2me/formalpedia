-- Prove2me | Theorems.Thm_CondEntanglement_dual_partyProduct
-- name    : CondEntanglement.dual_partyProduct
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:03:41.85406+00:00
-- url     : https://prove2.me/theorems/b58c2775-cbfd-4c91-992e-c32d652d156d
-- title:
--   $S_n$ of a party-wise product is the sum (eq. (9), p.3, $S_n$ form)
-- statement:
--   Throughout, $n$ parties hold finite-dimensional systems $A_1,\dots,A_n$; $S$ is the von Neumann entropy (in bits) and, for a state on $X_1\cdots X_n$,
--
--   $$
--   S_n(X_1:\cdots:X_n)=\sum_{i=1}^n S(X_1\cdots X_{i-1}X_{i+1}\cdots X_n)-(n-1)\,S(X_1\cdots X_n)
--   $$
--
--   is the **dual multipartite mutual information** (p.4). An **extension** of $\rho_{A_1\cdots A_n}$ is a state $\rho_{A_1A_1'\cdots A_nA_n'}$ with $\operatorname{Tr}_{A_1'\cdots A_n'}\rho_{A_1A_1'\cdots A_nA_n'}=\rho_{A_1\cdots A_n}$, one primed system $A_i'$ per party, and
--
--   $$
--   C_S(\rho)=\inf\{S_n(A_1A_1':\cdots:A_nA_n')-S_n(A_1':\cdots:A_n')\},
--   $$
--
--   the infimum over all extensions.
--
--   Let $\rho$ be a state on $A_1\cdots A_n$ and $\sigma$ a state on $B_1\cdots B_n$, and regard $\rho\otimes\sigma$ as an $n$-party state in which party $i$ holds $A_iB_i$. Then
--
--   $$
--   S_n(A_1B_1:\cdots:A_nB_n)_{\rho\otimes\sigma}=S_n(A_1:\cdots:A_n)_\rho+S_n(B_1:\cdots:B_n)_\sigma .
--   $$
--
--   Applied to two extensions $\rho_{A_1A_1'\cdots}$, $\sigma_{B_1B_1'\cdots}$ (whose product is an extension of $\rho\otimes\sigma$) and to their primed marginals, it gives the $S_n$ form of display (9) on p.3, $I(AA'CC':BB'DD')-I(A'C':B'D')=I(AA':BB')-I(A':B')+I(CC':DD')-I(C':D')$.
--
--   **Formalization Note** $S_n$ is `info .dual · (singleParties n) ∅` and $\rho\otimes\sigma$ is the published `partyProduct ρ σ`. Both inputs must be density matrices (the identity fails for unnormalized matrices).
--
--   Differences from the source:
--   - reading: display (9): the increment of a product of extensions is the sum of the increments stated for the bipartite C_I with the quantum mutual information I (p.3) → the same step for C_S with the dual multipartite information S_n; reason: p.4: 'All conclusions for the bipartite case can be similarly deduced.' licenses the transposition; Proposition 4 is proved only this way
--   - encoding: S, the von Neumann entropy, with the logarithm base unstated → QAlgorithms.vnEntropy, base 2 (bits); reason: every term of S_n is one multiple of log, so a common base gives the same statement
--   - generalization: the identity (9) for the increments of two extensions → S_n(ρ⊗σ) = S_n(ρ) + S_n(σ) for every pair of states; reason: (9) is this identity applied to the two extensions and to their primed marginals, then subtracted
--   - encoding: ρ_{A1⋯An} ⊗ σ_{B1⋯Bn} as an n-party state with party i = A_iB_i → partyProduct ρ σ on ∏_i (D i × F i), entries ρ(a,a′)·σ(b,b′); reason: the source's grouping (AC:BD on p.3, A_iB_i on p.4); same state
--   - generalization: multipartite states, n ≥ 2 parties → every n : ℕ; reason: for n ≤ 1, S_n ≡ 0 on states and both sides are 0; the case n ≥ 2 is the source's statement
-- source:
--   Yang–Horodecki–Wang, Conditional Entanglement, arXiv:quant-ph/0701149v3, display (9), p.3; transposed to S_n by p.4 ('All conclusions for the bipartite case can be similarly deduced')

import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33

namespace CondEntanglement

/-- Yang–Horodecki–Wang, *Conditional Entanglement*, arXiv:quant-ph/0701149v3, display (9), p.3:
"I(AA′CC′ : BB′DD′) − I(A′C′ : B′D′) = I(AA′ : BB′) − I(A′ : B′) + I(CC′ : DD′) − I(C′ : D′)",
the entropic identity behind it, transposed to the dual multipartite information `Sₙ` by p.4:
"All conclusions for the bipartite case can be similarly deduced."

For density matrices `ρ` on `A₁⋯Aₙ` (`Aᵢ = D i`) and `σ` on `B₁⋯Bₙ` (`Bᵢ = F i`), the
dual multipartite information of the party-wise product `ρ ⊗ σ`, in which party `i` holds
`AᵢBᵢ`, is the sum:
`Sₙ(A₁B₁ : ⋯ : AₙBₙ)_{ρ⊗σ} = Sₙ(A₁ : ⋯ : Aₙ)_ρ + Sₙ(B₁ : ⋯ : Bₙ)_σ`.
Applied to two extensions and to their primed marginals it gives the `Sₙ` form of (9).

**Formalization Note.** `Sₙ` is the published `info .dual · (singleParties n) ∅` (entropies in
bits); `partyProduct ρ σ` has entries `ρ(a,a′)·σ(b,b′)` with party `i` of the product holding
`(Dᵢ, Fᵢ)`, the AC:BD grouping of p.3. The identity is stated for every pair of states, not only
for extensions; the density-matrix hypotheses are needed (it fails for unnormalized matrices). -/
theorem dual_partyProduct {n : ℕ} {D F : Fin n → Type} [∀ i, Fintype (D i)]
    [∀ i, Fintype (F i)]
    (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (σ : Matrix (RegisterBasis F) (RegisterBasis F) ℂ)
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    info .dual (partyProduct ρ σ) (singleParties n) ∅ =
      info .dual ρ (singleParties n) ∅ + info .dual σ (singleParties n) ∅ := by sorry

end CondEntanglement
