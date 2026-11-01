-- Prove2me | Theorems.Thm_DattaDiscord_eq_8
-- name    : DattaDiscord.eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:28:25.263812+00:00
-- url     : https://prove2.me/theorems/d3bef014-b8a6-45c3-abed-eca8da8e1d23
-- title:
--   Eq. (8) — zero discord iff $\rho_{AB}=\sum_jp_j\rho_{A|j}\otimes|\lambda_j\rangle\langle\lambda_j|$ in an eigenbasis of $\rho_B$
-- statement:
--   Let $\rho_{AB}$ be a density matrix. Then $\mathcal D(A:B)=0$ if and only if there are
--
--   1. an orthonormal basis $\{|\lambda_j\rangle\}$ of $\mathcal H_B$ that diagonalizes $\rho_B$, i.e. $\rho_B=\sum_j\tau_j|\lambda_j\rangle\langle\lambda_j|$ with $\{\tau_j\}$ a probability vector,
--   2. a probability vector $\{p_j\}$, and
--   3. density matrices $\rho_{A|j}$ on $\mathcal H_A$,
--
--   such that
--
--   $$
--   \rho_{AB}=\sum_j p_j\,\rho_{A|j}\otimes|\lambda_j\rangle\langle\lambda_j| .
--   $$
--
--   Zero-discord states are thus exactly the classical–quantum states, classical on $B$ in an eigenbasis of the marginal $\rho_B$.
--
--   Differences from the source:
--   - reading: "ρAB = Σj pjρA|j ⊗ |λj⟩⟨λj| in the basis that diagonalizes ρB" → there exist an orthonormal basis {λ_j} with ρ_B = Σ_j τ_j |λ_j⟩⟨λ_j| (τ a probability vector), a probability vector p and density matrices σ_j on A with ρ_AB = Σ_j p_j σ_j ⊗ |λ_j⟩⟨λ_j|; reason: after "Relabelling" the ρ_{A|j} are arbitrary states of A, and "the basis" is one eigenbasis (when ρ_B has a repeated eigenvalue the "every eigenbasis" reading is false: ½(|00⟩⟨00| + |11⟩⟨11|) has zero discord but is not of this form in the |±⟩ basis); quantifying over arbitrary σ_j makes ⇐ at least as strong as with the measured ρ_{A|j}.
--   - reading: D(A, B), Eq. (2), whose two printed lines disagree → D = I − J from the first line, with the min as the infimum `minCondEntropy`; reason: the printed second line "H(A) − H(A : B) + min H̃" is −1 on the Bell state, against Theorem 1, so the first line is the definition; the minimum exists (milestone `minCondEntropy_attained`), so inf and min agree.
-- source:
--   Datta, A Condition for the Nullity of Quantum Discord, arXiv:1003.5256v2, Eq. (8), p.2 ("Relabelling, we have that the discord is zero if and only if ρAB = Σj pjρA|j ⊗ |λj⟩⟨λj| (8) in the basis that diagonalizes ρB")

import Definitions.Def_DattaDiscord_discord

open QAlgorithms (IsDensityMatrix vnEntropy traceLeft traceRight pureDensity)

namespace DattaDiscord

/-- **Eq. (8)**, Datta, *A Condition for the Nullity of Quantum Discord*, arXiv:1003.5256v2, p.2 ("Relabelling, we have that the discord is zero if and only if
ρAB = Σj pjρA|j ⊗ |λj⟩⟨λj| (8) in the basis that diagonalizes ρB"): the discord of a density
matrix `ρ_AB` is zero if and only if there are an orthonormal basis `{λ_j}` of `B` that
diagonalizes `ρ_B` (`ρ_B = ∑_j τ_j |λ_j⟩⟨λ_j|` with `{τ_j}` a probability vector), a probability
vector `{p_j}` and states `ρ_{A|j}` of `A` with `ρ_AB = ∑_j p_j ρ_{A|j} ⊗ |λ_j⟩⟨λ_j|`.

**Formalization Note** `A ⊗ B` is indexed by `A × B` with `A` the first factor; `ρ_B = traceLeft ρ`
and `ρ_A = traceRight ρ` (the published partial traces); a projector `P` on `B` acts as
`I_A ⊗ P = Matrix.kronecker 1 P`; entropies are the published `vnEntropy`, in bits. After "Relabelling" the `ρ_{A|j}` are arbitrary density matrices `σ_j` on `A`. -/
theorem eq_8 {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ) :
    discord ρ = 0 ↔
      ∃ (lam : OrthonormalBasis B ℂ (EuclideanSpace ℂ B)) (τ p : B → ℝ) (σ : B → Matrix A A ℂ),
        (∀ j, 0 ≤ τ j) ∧ ∑ j, τ j = 1 ∧
        traceLeft ρ = ∑ j, (τ j : ℂ) • pureDensity (lam j) ∧
        (∀ j, 0 ≤ p j) ∧ ∑ j, p j = 1 ∧ (∀ j, IsDensityMatrix (σ j)) ∧
        ρ = ∑ j, (p j : ℂ) • Matrix.kronecker (σ j) (pureDensity (lam j)) := by sorry

end DattaDiscord
