-- Prove2me | Theorems.Thm_DattaDiscord_minCondEntropy_attained
-- name    : DattaDiscord.minCondEntropy_attained
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:24:55.159386+00:00
-- url     : https://prove2.me/theorems/f1993573-d63f-4395-9349-44029e78ec76
-- title:
--   The minimum in Eq. (2) is attained at an extreme point that is a rank-one POVM (corrected: not every extreme point of the POVM set is rank one)
-- statement:
--   Let $\rho_{AB}$ be a density matrix on $\mathcal H_A\otimes\mathcal H_B$ (finite-dimensional, nonzero). Then there is a rank-one POVM $\{\Pi_i\}_{i=0}^{n-1}$ on $B$ with finitely many outcomes, which is an extreme point of the convex set of $n$-outcome POVMs on $B$, such that
--
--   $$
--   \tilde H_{\{\Pi_i\}}(A|B)=\tilde H(A|B)\qquad\text{and}\qquad \tilde H_{\{\Pi_i\}}(A|B)\le\tilde H_{\{M_j\}}(A|B)
--   $$
--
--   for every POVM $\{M_j\}$ on $B$ with finitely many outcomes. In words: the minimum of the measured conditional entropy over all measurements of $B$ exists and is attained at an extreme point of the set of POVMs that is rank one, so the "min" in the definition of discord is a true minimum.
--
--   This is the step that lets the paper restrict the discord to rank-one POVMs and treat its optimum as a minimizer.
--
--   Differences from the source:
--   - correction: "the minimum is attained on the extreme points of the set of POVMs, which are rank 1" → the minimum over all finite POVMs is attained at a POVM that is an extreme point of the set of POVMs with its number of outcomes and is rank one; reason: the extreme points of the set of POVMs are not all rank one (a projective measurement {P, I − P} with rank P = 2 on ℂ³ is extremal), so the claim "every extreme point is rank 1" is replaced by "some minimizing extreme point is rank 1" (true: the rank-one refinement of an extremal POVM is extremal and does not increase H̃).
--   - encoding: POVMs with a finite outcome set → POVMs indexed by `Fin n` for every n; reason: the paper bounds nothing, and every finite outcome set is some Fin n.
-- source:
--   Datta, A Condition for the Nullity of Quantum Discord, arXiv:1003.5256v2, p.1 ("the minimum is attained on the extreme points of the set of POVMs, which are rank 1")

import Definitions.Def_DattaDiscord_minCondEntropy

open QAlgorithms (IsDensityMatrix vnEntropy traceLeft traceRight pureDensity)

namespace DattaDiscord

/-- **The minimum in Eq. (2) is attained**, Datta, *A Condition for the Nullity of Quantum Discord*, arXiv:1003.5256v2, p.1 ("Since the conditional entropy is
concave over the set of POVMs, which is convex, the minimum is attained on the extreme points of
the set of POVMs, which are rank 1"): for every density matrix `ρ_AB` there is a rank-one POVM
`{Πᵢ}` on `B`, with finitely many outcomes `n`, that is an extreme point of the (convex) set of
`n`-outcome POVMs on `B` and whose measured conditional entropy is the minimum of
`H̃_{Mⱼ}(A|B)` over every POVM `{Mⱼ}` on `B` with finitely many outcomes, and so equals the infimum
`H̃(A|B)` over all rank-one POVMs.

The page's justification identifies the extreme points of the set of POVMs with the rank-one
POVMs; that identification is not exact (a projective measurement `{P, I − P}` with `rank P = 2`
on `ℂ³` is extremal), so the statement keeps the rest of the sentence: the minimum is attained
at an extreme point of the set of POVMs, and that extreme point can be taken rank one.

**Formalization Note** `A ⊗ B` is indexed by `A × B` with `A` the first factor; `ρ_B = traceLeft ρ`
and `ρ_A = traceRight ρ` (the published partial traces); a projector `P` on `B` acts as
`I_A ⊗ P = Matrix.kronecker 1 P`; entropies are the published `vnEntropy`, in bits. -/
theorem minCondEntropy_attained {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ) :
    ∃ (n : ℕ) (M : Fin n → Matrix B B ℂ), IsRankOnePOVM M ∧
      M ∈ Set.extremePoints ℝ {N : Fin n → Matrix B B ℂ | QAlgorithms.IsPOVM N} ∧
      measuredCondEntropy ρ M = minCondEntropy ρ ∧
      ∀ (m : ℕ) (N : Fin m → Matrix B B ℂ), QAlgorithms.IsPOVM N →
        measuredCondEntropy ρ M ≤ measuredCondEntropy ρ N := by sorry

end DattaDiscord
