-- Prove2me | Theorems.Thm_DattaDiscord_theorem_1
-- name    : DattaDiscord.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:28:21.984741+00:00
-- url     : https://prove2.me/theorems/4d0d2224-edb8-46bd-9cf7-00a418dfa5a3
-- title:
--   Theorem 1 — quantum discord is nonnegative
-- statement:
--   For every density matrix $\rho_{AB}$ on a finite-dimensional bipartite system,
--
--   $$
--   \mathcal D(A:B)\ \ge\ 0 .
--   $$
--
--   The paper's proof derives this from strong subadditivity of the von Neumann entropy, and the equality case is the subject of Theorem 2.
--
--   Differences from the source:
--   - reading: D(A, B), Eq. (2), whose two printed lines disagree → D = I − J from the first line, i.e. H(B) − H(A,B) + min H̃; reason: the printed second line "H(A) − H(A : B) + min H̃" equals H(A,B) − H(B) + min H̃, which is −1 on the Bell state, so it cannot be the quantity Theorem 1 calls nonnegative; the first line is the definition the text builds (D = I − J).
--   - encoding: min over rank-one POVMs in D → the infimum `minCondEntropy`; reason: the minimum exists (milestone `minCondEntropy_attained`), so the values agree.
-- source:
--   Datta, A Condition for the Nullity of Quantum Discord, arXiv:1003.5256v2, Theorem 1, p.1

import Definitions.Def_DattaDiscord_discord

open QAlgorithms (IsDensityMatrix vnEntropy traceLeft traceRight pureDensity)

namespace DattaDiscord

/-- **Theorem 1**, Datta, *A Condition for the Nullity of Quantum Discord*, arXiv:1003.5256v2, p.1: "Quantum discord is always positive, i.e., D(A, B) ≥ 0." For every
density matrix `ρ_AB`, `D(A : B) ≥ 0`.

**Formalization Note** `A ⊗ B` is indexed by `A × B` with `A` the first factor; `ρ_B = traceLeft ρ`
and `ρ_A = traceRight ρ` (the published partial traces); a projector `P` on `B` acts as
`I_A ⊗ P = Matrix.kronecker 1 P`; entropies are the published `vnEntropy`, in bits. -/
theorem theorem_1 {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ) :
    0 ≤ discord ρ := by sorry

end DattaDiscord
