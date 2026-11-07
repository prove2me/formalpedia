-- Prove2me | Theorems.Thm_FairTeamContracts_lemma_3_3
-- name    : FairTeamContracts.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:32:06.73323+00:00
-- url     : https://prove2.me/theorems/88448969-41ac-4ebc-aadd-92823473fde7
-- title:
--   Lemma 3.3 (corrected: $f(S)>0$) — a fair swap with $\alpha_i<\alpha_j$ leads to the equilibrium $S\setminus\{j\}$
-- statement:
--   Throughout, $f$ is a success function (monotone, $f(\emptyset)=0$, values in $[0,1]$) on the agents $N=[n]$, and the costs satisfy $c_i\ge0$.
--   Let $f$ be submodular and let $(S,\alpha)$ be a fair team contract with $f(S)>0$. If $i,j\in S$ satisfy $\alpha_i<\alpha_j$, then the unique equilibrium after swapping the contracts of $i$ and $j$ is
--
--   $$S_{i,j}=S\setminus\{j\}:$$
--
--   $S\setminus\{j\}$ is an equilibrium of the swapped contract, and it is the only one. The agent who receives the lower share after the swap stops exerting effort.
--
--   The paper's statement has no condition on $f(S)$, and it is false without one: for $n=2$, $f\equiv0$, $c=(0,0)$, $S=\{1,2\}$ and $\alpha=(0,\tfrac12)$, the contract is fair, but the only equilibrium after the swap is $S$.
--
--   Differences from the source:
--   - correction: no condition on f(S) → 0 < f S; reason: false at f(S) = 0: n = 2, f ≡ 0, c = 0, S = {1,2}, α = (0, 1/2) is fair (every agent is indifferent, so E = S is the only equilibrium and (1) reads 0 ≥ 0), but S_{1,2} = S ≠ S∖{2}
--   - reading: the lemma's S_{i,j}, defined in Definition 2.6 for submodular f → IsSubmodular f as a hypothesis; reason: Definition 2.6 defines the unique equilibrium only for submodular f (p.10), and the proof uses Proposition 2.5
--   - encoding: the unique equilibrium S_{i,j} satisfies S_{i,j} = S∖{j} → S∖{j} is a PNE of α ∘ swap i j, and every PNE of it equals S∖{j}; reason: existence and uniqueness of the equilibrium spelled out
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Lemma 3.3, p.11 (proof: Appendix B.1, p.38)

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_FairTeamContracts_IsSuccessFn
import Definitions.Def_FairTeamContracts_IsFair

namespace FairTeamContracts

/-- **Lemma 3.3, corrected: `f(S) > 0`** (Chen, Castiglioni, Li, *Fair Team Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Lemma 3.3, p.11; proof in
Appendix B.1, p.38). For a submodular success function and nonnegative costs, if the team
contract `(S, α)` is fair and `i, j ∈ S` have `αᵢ < αⱼ`, then the unique equilibrium `S_{i,j}`
after swapping the contracts of `i` and `j` is `S∖{j}`.

**Formalization Note.** The hypothesis `0 < f S` is a correction: with `f ≡ 0`, `c = 0`,
`S = {1, 2}`, `α = (0, 1/2)` the contract is fair, but the only equilibrium after the swap is `S`.
The conclusion states that `S∖{j}` is an equilibrium of the swapped contract and that every
equilibrium of it equals `S∖{j}` (Definition 2.6 is used only for submodular `f`, hence the
submodularity hypothesis). -/
theorem lemma_3_3 {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (hf : IsSuccessFn f) (hsub : SubsamplingSM.Offline.IsSubmodular f) (hc : ∀ i, 0 ≤ c i)
    (S : Finset (Fin n)) (α : Fin n → ℝ) (hfair : IsFair f c S α) (hfS : 0 < f S)
    (i j : Fin n) (hi : i ∈ S) (hj : j ∈ S) (hlt : α i < α j) :
    IsPNE f c S (α ∘ Equiv.swap i j) (S.erase j) ∧
      ∀ E : Finset (Fin n), IsPNE f c S (α ∘ Equiv.swap i j) E → E = S.erase j := by sorry

end FairTeamContracts
