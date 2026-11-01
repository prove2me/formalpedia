-- Prove2me | Theorems.Thm_DattaDiscord_eq_4
-- name    : DattaDiscord.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:22:54.058534+00:00
-- url     : https://prove2.me/theorems/be3f6f64-a4eb-429a-a971-973b8b5e4156
-- title:
--   Eqs. (3)–(4c) — the dilated state and its marginals
-- statement:
--   Let $\rho_{AB}$ be a density matrix, $\{|e_j\rangle\}$ an orthonormal basis of $\mathcal H_B$, and $\rho'_{ABC}$ the dilated state of Eq. (3). Write $p_j=\mathrm{Tr}\big((I_A\otimes|e_j\rangle\langle e_j|)\rho_{AB}\big)$ and $\rho_{A|j}$ for the outcome probabilities and post-measurement states of Eq. (1) for the measurement $\Pi_j=|e_j\rangle\langle e_j|$, and $\rho_B=\mathrm{Tr}_A\rho_{AB}$. Then $\rho'_{ABC}$ is a density matrix and
--
--   1. (4a) $\displaystyle\rho'_{AB}=\sum_j p_j\,\rho_{A|j}\otimes|e_j\rangle\langle e_j|=\sum_j P_j\,\rho_{AB}\,P_j$, where $P_j=I_A\otimes|e_j\rangle\langle e_j|$;
--   2. (4b) $\displaystyle\rho'_{BC}=\sum_{j,k}|e_j\rangle\langle e_j|\rho_B|e_k\rangle\langle e_k|\otimes|f_j\rangle\langle f_k|$;
--   3. (4c) $\displaystyle\rho'_B=\sum_j p_j\,|e_j\rangle\langle e_j|$.
--
--   These identities show that the dilated state carries the post-measurement ensemble on $AB$ and the coherent copy of $\rho_B$ on $BC$; the second form of (4a) is what connects Eq. (8) to the block-diagonal form of Theorem 2.
--
--   Differences from the source:
--   - generalization: (4a) as printed → (4a) together with ρ′_AB = Σ_j P_j ρ_AB P_j, and the conjunct that ρ′_ABC is a density matrix; reason: both are extra true conclusions (the paper calls ρ′_ABC "the state"); dropping them gives the printed statement.
--   - encoding: system C with basis {|f_j⟩} → C indexed by B with |f_j⟩⟨f_k| = Matrix.single j k 1; marginals by partial traces after re-associating (A × B) × C; reason: Lean convention, same operators.
--   - encoding: ρ_{A|j} for p_j = 0 → the zero matrix, multiplied by p_j = 0; reason: the term p_j ρ_{A|j} is 0 either way.
-- source:
--   Datta, A Condition for the Nullity of Quantum Discord, arXiv:1003.5256v2, Eq. (3) p.1; Eqs. (4a)–(4c), p.2

import Definitions.Def_DattaDiscord_dilated
import Definitions.Def_DattaDiscord_condState

open QAlgorithms (IsDensityMatrix vnEntropy traceLeft traceRight pureDensity)

namespace DattaDiscord

/-- **Eqs. (3), (4a)–(4c)**, Datta, *A Condition for the Nullity of Quantum Discord*, arXiv:1003.5256v2, pp.1–2: for a density matrix `ρ_AB` and an orthonormal basis
`{e_j}` of `B`, the dilated state `ρ′_ABC` of Eq. (3) is a density matrix, and its marginals are
* (4a) `ρ′_AB = ∑_j p_j ρ_{A|j} ⊗ |e_j⟩⟨e_j|`, which also equals `∑_j P_j ρ_AB P_j` with
  `P_j = I_A ⊗ |e_j⟩⟨e_j|`;
* (4b) `ρ′_BC = ∑_{j,k} |e_j⟩⟨e_j|ρ_B|e_k⟩⟨e_k| ⊗ |f_j⟩⟨f_k|`;
* (4c) `ρ′_B = ∑_j p_j |e_j⟩⟨e_j|`,
where `p_j` and `ρ_{A|j}` are those of Eq. (1) for `Π_j = |e_j⟩⟨e_j|`.

**Formalization Note** `A ⊗ B` is indexed by `A × B` with `A` the first factor; `ρ_B = traceLeft ρ`
and `ρ_A = traceRight ρ` (the published partial traces); a projector `P` on `B` acts as
`I_A ⊗ P = Matrix.kronecker 1 P`; entropies are the published `vnEntropy`, in bits. `ρ′_AB = traceRight ρ′_ABC` (trace out `C`); `ρ′_BC` is `traceLeft` of `ρ′_ABC` re-indexed
from `(A × B) × C` to `A × (B × C)`; `ρ′_B = traceRight ρ′_BC`; `|f_j⟩⟨f_k| = Matrix.single j k 1`.
The equality with `∑_j P_j ρ_AB P_j` is an extra conjunct (true, and not printed). -/
theorem eq_4 {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ)
    (e : OrthonormalBasis B ℂ (EuclideanSpace ℂ B)) :
    IsDensityMatrix (dilated e ρ) ∧
    traceRight (dilated e ρ) = ∑ j, Matrix.kronecker (1 : Matrix A A ℂ) (pureDensity (e j)) * ρ *
      Matrix.kronecker (1 : Matrix A A ℂ) (pureDensity (e j)) ∧
    traceRight (dilated e ρ) = ∑ j, (outcomeProb ρ (pureDensity (e j)) : ℂ) •
      Matrix.kronecker (condState ρ (pureDensity (e j))) (pureDensity (e j)) ∧
    traceLeft (Matrix.reindex (Equiv.prodAssoc A B B) (Equiv.prodAssoc A B B) (dilated e ρ)) =
      ∑ j, ∑ k, Matrix.kronecker (pureDensity (e j) * traceLeft ρ * pureDensity (e k))
        (Matrix.single j k (1 : ℂ)) ∧
    traceRight (traceLeft (Matrix.reindex (Equiv.prodAssoc A B B) (Equiv.prodAssoc A B B) (dilated e ρ))) =
      ∑ j, (outcomeProb ρ (pureDensity (e j)) : ℂ) • pureDensity (e j) := by sorry

end DattaDiscord
