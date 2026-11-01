-- Prove2me | Theorems.Thm_DattaDiscord_eq_4_entropies
-- name    : DattaDiscord.eq_4_entropies
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:22:44.552404+00:00
-- url     : https://prove2.me/theorems/cc46ea60-52e1-4435-b90d-ddfc82822a81
-- title:
--   Entropies of the dilated state, $H(\rho'_{ABC})=H(\rho_{AB})$, $H(\rho'_{AB})=H(\mathbf p)+\sum_jp_jH(A|j)$, $H(\rho'_{BC})=H(\rho_B)$, $H(\rho'_B)=H(\mathbf p)$
-- statement:
--   Let $\rho_{AB}$ be a density matrix, $\{|e_j\rangle\}$ an orthonormal basis of $\mathcal H_B$, $\rho'_{ABC}$ the dilated state of Eq. (3), and $p_j$, $\rho_{A|j}$ as in Eq. (1) for $\Pi_j=|e_j\rangle\langle e_j|$. With $H(\mathbf p)=-\sum_j p_j\log_2p_j$ the Shannon entropy and $H(A|j)=H(\rho_{A|j})$,
--
--   $$
--   H(\rho'_{ABC})=H(\rho_{AB}),\qquad H(\rho'_{AB})=H(\mathbf p)+\sum_j p_jH(A|j),\qquad H(\rho'_{BC})=H(\rho_B),\qquad H(\rho'_B)=H(\mathbf p).
--   $$
--
--   Substituted into strong subadditivity of $\rho'_{ABC}$, these identities give Eq. (6).
--
--   Differences from the source:
--   - encoding: H(p) → −Σ_j p_j log₂ p_j with Real.logb 2 (0 log 0 = 0); reason: the Shannon entropy in bits, as the paper's base-2 convention.
--   - encoding: H(A|j) for p_j = 0 → entropy of the zero matrix, multiplied by p_j = 0; reason: the term is 0 either way.
-- source:
--   Datta, A Condition for the Nullity of Quantum Discord, arXiv:1003.5256v2, p.2 ("whereby H(ρ′ABC) = H(ρAB)"; "whereby H(ρ′AB) = H(p) + Σj pjH(A|j), H(ρ′BC) = H(ρB) and H(ρ′B) = H(p) respectively")

import Definitions.Def_DattaDiscord_dilated
import Definitions.Def_DattaDiscord_condState

open QAlgorithms (IsDensityMatrix vnEntropy traceLeft traceRight pureDensity)

namespace DattaDiscord

/-- **The entropy identities after Eqs. (3) and (4c)**, Datta, *A Condition for the Nullity of Quantum Discord*, arXiv:1003.5256v2, p.2 ("whereby H(ρ′ABC) = H(ρAB)";
"whereby H(ρ′AB) = H(p) + Σj pjH(A|j), H(ρ′BC) = H(ρB) and H(ρ′B) = H(p) respectively"): for a
density matrix `ρ_AB` and an orthonormal basis `{e_j}` of `B`, with `p_j = Tr((I_A ⊗ |e_j⟩⟨e_j|) ρ_AB)`
and `H(A|j) = H(ρ_{A|j})`,
`H(ρ′_ABC) = H(ρ_AB)`, `H(ρ′_AB) = H(p) + ∑_j p_j H(A|j)`, `H(ρ′_BC) = H(ρ_B)`, `H(ρ′_B) = H(p)`.

**Formalization Note** `A ⊗ B` is indexed by `A × B` with `A` the first factor; `ρ_B = traceLeft ρ`
and `ρ_A = traceRight ρ` (the published partial traces); a projector `P` on `B` acts as
`I_A ⊗ P = Matrix.kronecker 1 P`; entropies are the published `vnEntropy`, in bits. `H(p) = −∑_j p_j log₂ p_j` is the Shannon entropy in bits (`Real.logb 2 0 = 0`, so
`0 log 0 = 0`); the marginals of `ρ′_ABC` are taken as in `eq_4`. -/
theorem eq_4_entropies {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ)
    (e : OrthonormalBasis B ℂ (EuclideanSpace ℂ B)) :
    vnEntropy (dilated e ρ) = vnEntropy ρ ∧
    vnEntropy (traceRight (dilated e ρ)) =
      (-∑ j, outcomeProb ρ (pureDensity (e j)) * Real.logb 2 (outcomeProb ρ (pureDensity (e j)))) +
      ∑ j, outcomeProb ρ (pureDensity (e j)) * vnEntropy (condState ρ (pureDensity (e j))) ∧
    vnEntropy (traceLeft (Matrix.reindex (Equiv.prodAssoc A B B) (Equiv.prodAssoc A B B) (dilated e ρ))) = vnEntropy (traceLeft ρ) ∧
    vnEntropy (traceRight (traceLeft (Matrix.reindex (Equiv.prodAssoc A B B) (Equiv.prodAssoc A B B) (dilated e ρ)))) =
      -∑ j, outcomeProb ρ (pureDensity (e j)) * Real.logb 2 (outcomeProb ρ (pureDensity (e j))) := by sorry

end DattaDiscord
