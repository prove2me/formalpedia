-- Prove2me | Theorems.Thm_DattaDiscord_eq_6
-- name    : DattaDiscord.eq_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:23:45.370868+00:00
-- url     : https://prove2.me/theorems/1d7c369c-1e80-4b4e-b5aa-d234068e561e
-- title:
--   Eq. (6) — $\tilde H_{\{\Pi_i\}}(A|B)\ge H(\rho_{AB})-H(\rho_B)$ for every rank-one POVM
-- statement:
--   Let $\rho_{AB}$ be a density matrix and $\{\Pi_i\}$ any rank-one POVM on $B$ with finitely many outcomes. Then
--
--   $$
--   \tilde H_{\{\Pi_i\}}(A|B)\ \ge\ H(\rho_{AB})-H(\rho_B)=H(A|B),
--   $$
--
--   the measured conditional entropy is at least the quantum conditional entropy. Taking the minimum over measurements gives Theorem 1 (nonnegativity of discord), and zero discord is equality here for a minimizing measurement.
--
--   Differences from the source:
--   - encoding: "all measurements" (rank-one POVMs, by the paper's standing convention) → rank-one POVMs indexed by Fin n for every n; reason: every finite outcome set is some Fin n.
-- source:
--   Datta, A Condition for the Nullity of Quantum Discord, arXiv:1003.5256v2, Eq. (6), p.2 ("This, being true for all measurements, also holds for the minimum")

import Definitions.Def_DattaDiscord_IsRankOnePOVM
import Definitions.Def_DattaDiscord_measuredCondEntropy

open QAlgorithms (IsDensityMatrix vnEntropy traceLeft traceRight pureDensity)

namespace DattaDiscord

/-- **Eq. (6)**, Datta, *A Condition for the Nullity of Quantum Discord*, arXiv:1003.5256v2, p.2: for every rank-one POVM `{Πᵢ}` on `B` ("This, being true for all
measurements"), the measured conditional entropy is at least the quantum conditional entropy,
`H̃_{Πᵢ}(A|B) ≥ H(ρ_AB) − H(ρ_B)`.

**Formalization Note** `A ⊗ B` is indexed by `A × B` with `A` the first factor; `ρ_B = traceLeft ρ`
and `ρ_A = traceRight ρ` (the published partial traces); a projector `P` on `B` acts as
`I_A ⊗ P = Matrix.kronecker 1 P`; entropies are the published `vnEntropy`, in bits. The POVM has any finite number `n` of outcomes. -/
theorem eq_6 {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ)
    {n : ℕ} (M : Fin n → Matrix B B ℂ) (hM : IsRankOnePOVM M) :
    vnEntropy ρ - vnEntropy (traceLeft ρ) ≤ measuredCondEntropy ρ M := by sorry

end DattaDiscord
