-- Prove2me | Theorems.Thm_FairTeamContracts_lemma_3_4
-- name    : FairTeamContracts.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:32:05.13669+00:00
-- url     : https://prove2.me/theorems/56a6e1fb-b305-47b5-b92c-76b2422fc7f4
-- title:
--   Lemma 3.4 (corrected: $f(S)>0$) — fairness is equivalent to condition (3)
-- statement:
--   Throughout, $f$ is a success function (monotone, $f(\emptyset)=0$, values in $[0,1]$) on the agents $N=[n]$, and the costs satisfy $c_i\ge0$.
--   Let $f$ be submodular, and let $(S,\alpha)$ be a feasible team contract with $f(S)>0$. Then $(S,\alpha)$ is fair if and only if every pair $i,j\in S$ with $\alpha_i<\alpha_j$ satisfies
--
--   $$\frac{c_j}{f(j\mid S\setminus\{j\})}\ >\ \alpha_i\ \ge\ \alpha_j\,\frac{f(S\setminus\{j\})}{f(S)}.\qquad(3)$$
--
--   The fairness test, which quantifies over equilibria of all swapped contracts, thus reduces to explicit pairwise inequalities between shares and cut-off wages. It is the basis of the minimum-share characterization (Theorem 3.2).
--
--   The paper's statement has no condition on $f(S)$; the "only if" direction is false without one (same instance as for Lemma 3.3: $f\equiv0$, $c=0$, $\alpha=(0,\tfrac12)$ is fair, but (3) reads $0>0$).
--
--   Differences from the source:
--   - correction: no condition on f(S) → 0 < f S; reason: the only-if direction is false at f(S) = 0: n = 2, f ≡ 0, c = 0, S = {1,2}, α = (0, 1/2) is fair, but (3) for i = 1, j = 2 reads 0/0 = 0 > 0
--   - encoding: a team contract (S, α) → hypotheses IsTeamContract S α and IsFeasible f c S α; reason: the paper assumes feasibility of every team contract it considers (p.8)
--   - encoding: cⱼ/f(j|S∖{j}) with c/0 = ∞ → cutoff with Lean's c/0 = 0; reason: differs only when cⱼ > 0 = f(j|S∖{j}), which feasibility excludes
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Lemma 3.4, p.12 (proof: Appendix B.2, pp.38–39)

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_FairTeamContracts_IsSuccessFn
import Definitions.Def_FairTeamContracts_IsFair
import Definitions.Def_FairTeamContracts_marg

namespace FairTeamContracts

/-- **Lemma 3.4, corrected: `f(S) > 0`** (Chen, Castiglioni, Li, *Fair Team Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Lemma 3.4, p.12; proof in
Appendix B.2, pp.38–39). For a submodular success function and nonnegative costs, a (feasible)
team contract `(S, α)` with `f(S) > 0` is fair if and only if for every pair `i, j ∈ S` with
`αᵢ < αⱼ`,
`cⱼ / f(j | S∖{j}) > αᵢ ≥ αⱼ · f(S∖{j}) / f(S)`  (3).

**Formalization Note.** Feasibility is the paper's standing assumption on every team contract
(p.8). `cutoff f c S j` is `cⱼ / f(j | S∖{j})` with Lean's `x / 0 = 0`; the paper's `c/0 = ∞`
would differ only when `cⱼ > 0 = f(j | S∖{j})`, which feasibility excludes. The hypothesis
`0 < f S` is a correction: with `f ≡ 0`, `c = 0`, `S = {1, 2}`, `α = (0, 1/2)` the contract is
fair but (3) fails for `i = 1, j = 2`. -/
theorem lemma_3_4 {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (hf : IsSuccessFn f) (hsub : SubsamplingSM.Offline.IsSubmodular f) (hc : ∀ i, 0 ≤ c i)
    (S : Finset (Fin n)) (α : Fin n → ℝ) (hα : IsTeamContract S α) (hfeas : IsFeasible f c S α)
    (hfS : 0 < f S) :
    IsFair f c S α ↔ ∀ i ∈ S, ∀ j ∈ S, α i < α j →
      α i < cutoff f c S j ∧ α j * (f (S.erase j) / f S) ≤ α i := by sorry

end FairTeamContracts
