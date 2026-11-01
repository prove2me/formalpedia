-- Prove2me | Theorems.Thm_CondEntanglement_dualIncrement_nonneg
-- name    : CondEntanglement.dualIncrement_nonneg
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:04:28.094046+00:00
-- url     : https://prove2.me/theorems/7b786405-6601-4b65-a6ab-1c055f384b75
-- title:
--   $S_n$ does not increase when the unprimed systems are traced out ($C_S\ge0$; item 2, p.3, $S_n$ form)
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
--   Let $\omega$ be any state on $A_1A_1'\cdots A_nA_n'$, with arbitrary finite systems $A_i$, $A_i'$. Then
--
--   $$
--   S_n(A_1A_1':\cdots:A_nA_n')_\omega\;\ge\;S_n(A_1':\cdots:A_n')_\omega .
--   $$
--
--   This is the $S_n$ form of item 2 on p.3, "$C_I\ge0$ comes from the fact that the quantum mutual information is non-increasing under tracing subsystems of both sides", which p.4 transfers to the multipartite measures ("All conclusions for the bipartite case can be similarly deduced"). It gives $C_S\ge0$ and makes the infimum defining $C_S$ finite.
--
--   **Formalization Note** The statement is `0 ≤ CondEntanglement.dualIncrement ω` for every density matrix `ω`, the primed systems being arbitrary finite types `F i` (an empty one admits no state). Strong subadditivity (reference item `Gap48.P20.strongSubadditivity`) is the expected substrate.
--
--   Differences from the source:
--   - reading: C_I ≥ 0: I non-increasing under tracing subsystems stated for the bipartite C_I with the quantum mutual information I (p.3) → the same step for C_S with the dual multipartite information S_n; reason: p.4: 'All conclusions for the bipartite case can be similarly deduced.' licenses the transposition; Proposition 4 is proved only this way
--   - encoding: S, the von Neumann entropy, with the logarithm base unstated → QAlgorithms.vnEntropy, base 2 (bits); reason: every term of S_n is one multiple of log, so a common base gives the same statement
--   - generalization: the inequality is used for the extensions in the infimum (primed systems Fin d_i) → every density matrix on ∏_i (D i × F i) with arbitrary finite F i; reason: every extension is such a matrix, so the source's case is an instance
--   - generalization: multipartite states, n ≥ 2 parties → every n : ℕ; reason: for n ≤ 1, S_n ≡ 0 on states and both sides are 0; the case n ≥ 2 is the source's statement
-- source:
--   Yang–Horodecki–Wang, Conditional Entanglement, arXiv:quant-ph/0701149v3, item 2 (C_I ≥ 0), p.3; transposed to S_n by p.4 ('All conclusions for the bipartite case can be similarly deduced')

import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Definitions.Def_CondEntanglement_dualIncrement

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33

namespace CondEntanglement

/-- Yang–Horodecki–Wang, *Conditional Entanglement*, arXiv:quant-ph/0701149v3, p.3, item "2.":
"CI ≥0 comes from the fact that the quantum mutual information is non-increasing under tracing
subsystems of both sides", transposed to the dual multipartite information `Sₙ` by p.4: "All
conclusions for the bipartite case can be similarly deduced."

For every density matrix `ω` on `n` paired registers `AᵢA′ᵢ` (`Aᵢ = D i`, `A′ᵢ = F i`),
`Sₙ(A₁A′₁ : ⋯ : AₙA′ₙ) ≥ Sₙ(A′₁ : ⋯ : A′ₙ)`: `Sₙ` does not increase when the unprimed parts
`A₁, …, Aₙ` are traced out. Equivalently `0 ≤ dualIncrement ω`.

**Formalization Note.** The primed registers are arbitrary finite types `F i` (possibly empty, in
which case no density matrix exists and the claim is vacuous), not only `Fin dᵢ`; this covers
every extension in `csValues`. Entropies in bits (`QAlgorithms.vnEntropy`); every `n` is
allowed (for `n ≤ 1` both sides vanish). -/
theorem dualIncrement_nonneg {n : ℕ} {D F : Fin n → Type} [∀ i, Fintype (D i)]
    [∀ i, Fintype (F i)]
    (ω : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ)
    (hω : IsDensityMatrix ω) :
    0 ≤ dualIncrement ω := by sorry

end CondEntanglement
