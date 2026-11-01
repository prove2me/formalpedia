-- Prove2me | Theorems.Thm_CondEntanglement_cs_additive
-- name    : CondEntanglement.cs_additive
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:06:42.479457+00:00
-- url     : https://prove2.me/theorems/381c49c6-916e-401c-b25b-ef563a93307e
-- title:
--   Proposition 4, $C_S$ line: $C_S(\rho\otimes\sigma)=C_S(\rho)+C_S(\sigma)$ (the $C_I$ line is the referenced Gap20.P10.multipartite_additivity)
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
--   Let $\rho$ be a state on $A_1\cdots A_n$ and $\sigma$ a state on $B_1\cdots B_n$ (finite systems of arbitrary, possibly different, dimensions), and regard $\rho\otimes\sigma$ as an $n$-party state in which party $i$ holds $A_iB_i$. Then
--
--   $$
--   C_S(\rho_{A_1\cdots A_n}\otimes\sigma_{B_1\cdots B_n})=C_S(\rho_{A_1\cdots A_n})+C_S(\sigma_{B_1\cdots B_n}).
--   $$
--
--   This is the second line of Proposition 4 (p.4): the conditional entanglement built on the dual multipartite mutual information is additive. The first line, the same statement for $C_I$ (built on $I_n=\sum_iS(A_i)-S(A_1\cdots A_n)$), is the published and proved `QAlgorithms.Papers.Independent.Gap20.P10.multipartite_additivity`, a reference item of this mission; at $n=2$ it is Proposition 2, the paper's headline.
--
--   **Formalization Note** $C_S$ is `CondEntanglement.cs` (real infimum over all extensions with primed systems `Fin (d i)`, `0 < d i`, uncapped; no $\tfrac12$; bits) and $\rho\otimes\sigma$ is the published `partyProduct ρ σ`.
--
--   Differences from the source:
--   - encoding: S, the von Neumann entropy, with the logarithm base unstated → QAlgorithms.vnEntropy, base 2 (bits); reason: every term of S_n is one multiple of log, so a common base gives the same statement
--   - encoding: infimum over all extensions, ancilla systems A′_i of unspecified finite dimension → real sInf over d : Fin n → ℕ with 0 < d i, primed register Fin (d i), density matrix ω with unprimedMarginal ω = ρ; reason: every finite ancilla is some Fin d_i up to relabeling; the value set is nonempty and bounded below by 0 for states, so sInf is the infimum
--   - encoding: ρ_{A1⋯An} ⊗ σ_{B1⋯Bn} as an n-party state with party i = A_iB_i → partyProduct ρ σ on ∏_i (D i × F i), entries ρ(a,a′)·σ(b,b′); reason: the source's grouping (AC:BD on p.3, A_iB_i on p.4); same state
--   - generalization: multipartite states, n ≥ 2 parties → every n : ℕ; reason: for n ≤ 1, S_n ≡ 0 on states and both sides are 0; the case n ≥ 2 is the source's statement
-- source:
--   Yang–Horodecki–Wang, Conditional Entanglement, arXiv:quant-ph/0701149v3, Proposition 4, second line (C_S), p.4

import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Definitions.Def_CondEntanglement_cs

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33

namespace CondEntanglement

/-- Yang–Horodecki–Wang, *Conditional Entanglement*, arXiv:quant-ph/0701149v3, Proposition 4,
p.4, second line: "The conditional entanglement for multipartite mutual information is additive.
… C_S(ρ_{A₁⋯Aₙ} ⊗ σ_{B₁⋯Bₙ}) = C_S(ρ_{A₁⋯Aₙ}) + C_S(σ_{B₁⋯Bₙ})."

For density matrices `ρ` on `A₁⋯Aₙ` (`Aᵢ = D i`) and `σ` on `B₁⋯Bₙ` (`Bᵢ = F i`), the
conditional entanglement of the dual multipartite mutual information is additive on the
party-wise product (party `i` holds `AᵢBᵢ`).

The first line of Proposition 4 (the `C_I` clause, built on `Iₙ`) is the published, Proved
`QAlgorithms.Papers.Independent.Gap20.P10.multipartite_additivity`, a reference item of this
mission; this theorem is the `C_S` clause.

**Formalization Note.** `C_S` is `CondEntanglement.cs`: the real infimum of
`Sₙ(A₁A′₁ : ⋯ : AₙA′ₙ) − Sₙ(A′₁ : ⋯ : A′ₙ)` over all density-matrix extensions with primed
registers `Fin dᵢ`, `0 < dᵢ`, uncapped; no `1/2`; entropies in bits. Every `n` is allowed (for
`n ≤ 1`, `Sₙ ≡ 0` and both sides are `0`), as are unequal finite local dimensions in `ρ` and
`σ`. -/
theorem cs_additive {n : ℕ} {D F : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (σ : Matrix (RegisterBasis F) (RegisterBasis F) ℂ)
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    cs (partyProduct ρ σ) = cs ρ + cs σ := by sorry

end CondEntanglement
