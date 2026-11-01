-- Prove2me | Theorems.Thm_CondEntanglement_cs_partyProduct_ge
-- name    : CondEntanglement.cs_partyProduct_ge
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:06:20.840097+00:00
-- url     : https://prove2.me/theorems/f4ab8f52-85b5-44a7-87dd-7fc9e7b1cf19
-- title:
--   $C_S(\rho)+C_S(\sigma)\le C_S(\rho\otimes\sigma)$ (eq. (10), p.3, $C_S$ form)
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
--   C_S(\rho_{A_1\cdots A_n})+C_S(\sigma_{B_1\cdots B_n})\;\le\;C_S(\rho_{A_1\cdots A_n}\otimes\sigma_{B_1\cdots B_n}).
--   $$
--
--   This is the superadditive half of Proposition 4 for $C_S$: the $C_S$ form of display (10) and "This means that $C_I(\rho_{AB}\otimes\sigma_{CD})\ge C_I(\rho_{AB})+C_I(\sigma_{CD})$" (p.3), which p.4 transfers to the multipartite measures.
--
--   **Formalization Note** $C_S$ is `CondEntanglement.cs` and $\rho\otimes\sigma$ is `partyProduct ρ σ`.
--
--   Differences from the source:
--   - reading: C_I(ρ⊗σ) ≥ C_I(ρ) + C_I(σ), via (10) stated for the bipartite C_I with the quantum mutual information I (p.3) → the same step for C_S with the dual multipartite information S_n; reason: p.4: 'All conclusions for the bipartite case can be similarly deduced.' licenses the transposition; Proposition 4 is proved only this way
--   - encoding: S, the von Neumann entropy, with the logarithm base unstated → QAlgorithms.vnEntropy, base 2 (bits); reason: every term of S_n is one multiple of log, so a common base gives the same statement
--   - encoding: infimum over all extensions, ancilla systems A′_i of unspecified finite dimension → real sInf over d : Fin n → ℕ with 0 < d i, primed register Fin (d i), density matrix ω with unprimedMarginal ω = ρ; reason: every finite ancilla is some Fin d_i up to relabeling; the value set is nonempty and bounded below by 0 for states, so sInf is the infimum
--   - encoding: ρ_{A1⋯An} ⊗ σ_{B1⋯Bn} as an n-party state with party i = A_iB_i → partyProduct ρ σ on ∏_i (D i × F i), entries ρ(a,a′)·σ(b,b′); reason: the source's grouping (AC:BD on p.3, A_iB_i on p.4); same state
--   - generalization: multipartite states, n ≥ 2 parties → every n : ℕ; reason: for n ≤ 1, S_n ≡ 0 on states and both sides are 0; the case n ≥ 2 is the source's statement
-- source:
--   Yang–Horodecki–Wang, Conditional Entanglement, arXiv:quant-ph/0701149v3, proof of Proposition 2, display (10) and the sentence after it, p.3; transposed to C_S by p.4 ('All conclusions for the bipartite case can be similarly deduced')

import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Definitions.Def_CondEntanglement_cs

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33

namespace CondEntanglement

/-- Yang–Horodecki–Wang, *Conditional Entanglement*, arXiv:quant-ph/0701149v3, display (10) and
the sentence after it, p.3: "This means that CI(ρAB ⊗ σCD) ≥ CI(ρAB) + CI(σCD)", transposed to
`C_S` by p.4: "All conclusions for the bipartite case can be similarly deduced."

For density matrices `ρ` on `A₁⋯Aₙ` and `σ` on `B₁⋯Bₙ`,
`C_S(ρ) + C_S(σ) ≤ C_S(ρ ⊗ σ)`, the product being taken party-wise (party `i` holds `AᵢBᵢ`).

**Formalization Note.** `C_S` is `CondEntanglement.cs` (real infimum over all extensions with
positive finite primed dimensions, no `1/2`, entropies in bits); `partyProduct` is the published
party-wise product. Every `n` and all finite local dimensions are allowed. -/
theorem cs_partyProduct_ge {n : ℕ} {D F : Fin n → Type} [∀ i, Fintype (D i)]
    [∀ i, Fintype (F i)]
    (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (σ : Matrix (RegisterBasis F) (RegisterBasis F) ℂ)
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    cs ρ + cs σ ≤ cs (partyProduct ρ σ) := by sorry

end CondEntanglement
