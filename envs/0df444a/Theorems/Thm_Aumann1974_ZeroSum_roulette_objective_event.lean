-- Prove2me | Theorems.Thm_Aumann1974_ZeroSum_roulette_objective_event
-- name    : Aumann1974.ZeroSum.roulette_objective_event
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:04:38.69287+00:00
-- url     : https://prove2.me/theorems/e5782f18-6c5a-419c-8083-838bb7903188
-- title:
--   Lemma 7.1 — a roulette contains an objective event of any probability $\alpha$ independent of given events
-- statement:
--   Let $(\Omega,\mathcal B,(\mathcal J_i),(p_i))$ be a randomizing structure for a finite set $N$ of players satisfying Assumption II. Let $\mathcal R \subseteq \mathcal B$ be a **roulette**, i.e. a sub-$\sigma$-field on which every subjective probability $p_j$ is non-atomic, and let $B^1,\dots,B^l \in \mathcal B$ be events ($l \ge 0$). Then for every $\alpha \in [0,1]$ there is an event $A \in \mathcal R$ that is objective with probability $\alpha$ and independent of each $B^k$:
--   $$p_i(A) = \alpha \quad\text{and}\quad p_i(A\cap B^k) = p_i(A)\,p_i(B^k)\qquad\text{for all } i\in N,\ k=1,\dots,l.$$
--
--   This is the basic construction behind the paper's existence results: it produces objective randomization devices of arbitrary probability that do not interfere with a finite list of other events. Lemmas 4.2 and 4.4 are its special cases for the roulettes $\mathcal R_i$ of Assumption II and for a public roulette.
--
--   **Formalization Note** Assumption II is the paper's standing assumption from p. 75 and is included as a hypothesis, although this lemma only needs the roulette $\mathcal R$. Probabilities are compared in $[0,\infty]$, with $\alpha$ embedded as `ENNReal.ofReal α`.
-- source:
--   R. J. Aumann, Subjectivity and Correlation in Randomized Strategies, J. Math. Econ. 1 (1974) 67–96, https://doi.org/10.1016/0304-4068(74)90037-8, p. 81 (PDF p. 15), Lemma 7.1; proof pp. 81–82 (PDF pp. 15–16); roulette defined p. 77 (PDF p. 11)

import Mathlib
import Definitions.Def_Aumann1974_ZeroSum_RandomizingStructure

namespace Aumann1974.ZeroSum

open MeasureTheory

/-- **Lemma 7.1** (Aumann 1974, *Subjectivity and Correlation in Randomized Strategies*,
J. Math. Econ. 1, p. 81, PDF p. 15): let `ℛ` be a roulette, and let `B¹, …, Bˡ` be events. Then
for any `α` between `0` and `1`, there is an objective event in `ℛ` with probability `α` that is
independent of each of the `Bᵏ`.

**Formalization Note.** The roulette `ℛ` is the σ-algebra `m` (`IsRoulette`: `m ≤ ℬ` and every
`pⱼ` is non-atomic on `m`). The events `Bᵏ` are indexed by `Fin l` (`l = 0` allowed) and are
`ℬ`-measurable. "Objective with probability `α`" is `pᵢ(A) = α` for every player `i`;
"independent of `Bᵏ`" is `pᵢ(A ∩ Bᵏ) = pᵢ(A)pᵢ(Bᵏ)` for every player `i` (the last line of the
proof, p. 82). The players form a finite type (the paper's finite `N`). Assumption II, the
paper's standing assumption from p. 75, is carried as a hypothesis although the lemma's proof
does not use it. -/
theorem roulette_objective_event {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    (R : RandomizingStructure ι Ω mΩ) (hII : AssumptionII R)
    (m : MeasurableSpace Ω) (hm : IsRoulette R m)
    {l : ℕ} (B : Fin l → Set Ω) (hB : ∀ k, MeasurableSet[mΩ] (B k))
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ A : Set Ω, MeasurableSet[m] A ∧ IsObjective R A ∧
      (∀ i, R.p i A = ENNReal.ofReal α) ∧
      ∀ k, IsIndependentOf R A (B k) := by sorry

end Aumann1974.ZeroSum
