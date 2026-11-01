-- Prove2me | Theorems.Thm_DattaDiscord_theorem_2
-- name    : DattaDiscord.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:28:30.316377+00:00
-- url     : https://prove2.me/theorems/be3fd5b6-f958-40f2-87ab-44c3cb0d3b8e
-- title:
--   Theorem 2 — $\mathcal D(A:B)=0$ iff $\rho_{AB}$ is block-diagonal in an eigenbasis of $\rho_B$ (corrected: $\rho_B=\sum_j\tau_jP_j$ for the printed $\rho_{AB}=\sum_j\tau_jP_j$)
-- statement:
--   Let $A$ and $B$ be finite-dimensional quantum systems and $\rho_{AB}$ a density matrix on $\mathcal H_A\otimes\mathcal H_B$, with marginal $\rho_B=\mathrm{Tr}_A\rho_{AB}$. Then $\mathcal D(A:B)=0$ if and only if there are an orthonormal basis $\{|e_j\rangle\}$ of $\mathcal H_B$ and a probability vector $\{\tau_j\}$ with
--
--   $$
--   \rho_B=\sum_j\tau_j\,|e_j\rangle\langle e_j|
--   \qquad\text{and}\qquad
--   \rho_{AB}=\sum_j P_j\,\rho_{AB}\,P_j,\quad P_j=I_A\otimes|e_j\rangle\langle e_j| .
--   $$
--
--   That is, a state has zero quantum discord exactly when it is block-diagonal in an eigenbasis of the marginal of the measured system $B$. The discord here is $\mathcal D(A:B)=I(A:B)-\mathcal J(A:B)$, minimized over all rank-one POVMs on $B$ with any finite number of outcomes.
--
--   Differences from the source:
--   - correction: "where ρAB = Σj τjPj" and "the state ρAB is joint density operator is block-diagonal" → ρ_B = Σ_j τ_j |e_j⟩⟨e_j|, and "the state ρ_AB is block-diagonal"; reason: as printed the theorem is false: with P_j = I_A ⊗ |e_j⟩⟨e_j|, Σ_j τ_j P_j has trace dim A, so for dim A = 2 no density matrix ρ_AB equals it, yet ρ_AB = |00⟩⟨00| has D = 0; the subscript is a typo for ρ_B (the proof ends "in the basis that diagonalizes ρB"), and the second phrase is a garbled merge with no mathematical content.
--   - reading: "the marginal eigenbasis of B", projectors P_j → P_j = I_A ⊗ |e_j⟩⟨e_j| for some orthonormal eigenbasis {e_j} of ρ_B (existential); reason: with the spectral projectors of ρ_B the theorem is false (the Bell state |Φ⁺⟩⟨Φ⁺| has ρ_B = I/2, single projector I, so ρ_AB = Σ P_j ρ_AB P_j, yet D = 1; this reading also contradicts "{τj} a probability distribution"), and with "every eigenbasis" ⇒ is false (½(|00⟩⟨00| + |11⟩⟨11|) has D = 0 but is not block-diagonal in the |±⟩ eigenbasis of ρ_B = I/2).
--   - reading: D(A, B), Eq. (2), whose two printed lines disagree → D = I − J from the first line, i.e. H(B) − H(A,B) + min H̃; reason: the printed second line "H(A) − H(A : B) + min H̃" is a sign slip (it gives the Bell state discord −1, against Theorem 1).
--   - encoding: min over rank-one POVMs → the infimum `minCondEntropy` over rank-one POVMs indexed by Fin n, every n; reason: the minimum exists (milestone `minCondEntropy_attained`), so the values agree.
--   - encoding: finite-dimensional H_A, H_B; P_j acting on A ⊗ B → finite index types A, B with A the first factor; P_j = Matrix.kronecker 1 (pureDensity e_j); reason: Lean convention; same instances.
-- source:
--   Datta, A Condition for the Nullity of Quantum Discord, arXiv:1003.5256v2, Theorem 2, p.2

import Definitions.Def_DattaDiscord_discord

open QAlgorithms (IsDensityMatrix vnEntropy traceLeft traceRight pureDensity)

namespace DattaDiscord

/-- **Theorem 2**, Datta, *A Condition for the Nullity of Quantum Discord*, arXiv:1003.5256v2, p.2: `D(A, B) = 0` if and only if the state `ρ_AB` is block-diagonal in
the marginal eigenbasis of `B`, that is `ρ_AB = ∑_j P_j ρ_AB P_j`, where `ρ_B = ∑_j τ_j P_j` with
`{τ_j}` a probability distribution: for every density matrix `ρ_AB`, the discord is zero if and
only if there are an orthonormal basis `{e_j}` of `B` and a probability vector `{τ_j}` with
`ρ_B = ∑_j τ_j |e_j⟩⟨e_j|` and `ρ_AB = ∑_j P_j ρ_AB P_j`, `P_j = I_A ⊗ |e_j⟩⟨e_j|`.

**Formalization Note** `A ⊗ B` is indexed by `A × B` with `A` the first factor; `ρ_B = traceLeft ρ`
and `ρ_A = traceRight ρ` (the published partial traces); a projector `P` on `B` acts as
`I_A ⊗ P = Matrix.kronecker 1 P`; entropies are the published `vnEntropy`, in bits. The printed "where ρAB = Σj τjPj" is read as `ρ_B` (a subscript typo), and `P_j` are the
rank-one projectors of some orthonormal eigenbasis of `ρ_B` (existential). -/
theorem theorem_2 {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ) :
    discord ρ = 0 ↔
      ∃ (e : OrthonormalBasis B ℂ (EuclideanSpace ℂ B)) (τ : B → ℝ),
        (∀ j, 0 ≤ τ j) ∧ ∑ j, τ j = 1 ∧
        traceLeft ρ = ∑ j, (τ j : ℂ) • pureDensity (e j) ∧
        ρ = ∑ j, Matrix.kronecker (1 : Matrix A A ℂ) (pureDensity (e j)) * ρ *
          Matrix.kronecker (1 : Matrix A A ℂ) (pureDensity (e j)) := by sorry

end DattaDiscord
