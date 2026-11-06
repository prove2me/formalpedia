-- Prove2me | Theorems.Thm_CoverModular_proposition_2_greedy_type_approximation
-- name    : CoverModular.proposition_2_greedy_type_approximation
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:50.332379+00:00
-- url     : https://prove2.me/theorems/f844af56-0be5-4f41-bb2e-55ad74187c2e
-- title:
--   Proposition 2 — every heuristic of Algorithm 1 is a $\frac{1-(1-2/K)^K}{2}\ge\frac{1-e^{-2}}{2}$ approximation for flexibility design
-- statement:
--   Any iterative heuristic that fits the description of Algorithm 1 achieves an approximation factor of $\frac{1-(1-2/K)^K}{2}\ge\frac{1-e^{-2}}{2}\approx0.432$ for the budgeted flexibility design problem.
--
--   Precisely: let $(\mu,c,d,p)$ be a flexibility design instance with $\mu_\omega,c_{i\omega},d_{j\omega},p_{ij}\ge0$, let $K\ge1$ be the budget, let $P$ be a constant with $P\ge p_{ij}$ for all arcs, and let $\mathcal A_0,\dots,\mathcal A_K$ be any run of Algorithm 1 (any choice of optimal LP solutions and of admissible arcs). Then
--
--   1. $|\mathcal A_K|\le K$, so $\mathcal A_K$ is feasible for (FDP);
--   2. for every structure $\mathcal A$ with $|\mathcal A|\le K$,
--   $$
--   F(\mathcal A_K)\ge\frac{1-\bigl(1-\frac2K\bigr)^K}{2}\,F(\mathcal A);
--   $$
--   3. $\dfrac{1-(1-2/K)^K}{2}\ge\dfrac{1-e^{-2}}{2}$.
--
--   Natural greedy, which adds the arc of largest marginal gain, is one such heuristic, as are the cheaper primal and primal–dual greedy methods that need one LP per scenario and iteration. The guarantee is close to the $1-1/e$ hardness threshold of Proposition 1.
--
--   **Formalization Note** "Approximation factor" (Definition 1) is stated against every feasible structure, which is equivalent to the bound against the optimum $\max_{|\mathcal A|\le K}F(\mathcal A)$. The gloss $\approx0.432$ is not stated.
--
--   Differences from the source:
--   - encoding: capacities c_iω and demands d_jω carry no printed sign → c_iω ≥ 0 and d_jω ≥ 0 (in FDPInstance.Standing); reason: they are capacities and demands; LP (1) is infeasible otherwise and display (6) splits only into > 0 and = 0, so only instances where F is undefined are excluded
--   - encoding: f(𝒜, ω) = max of LP (1) → lpValue = sSup of the objective values over the feasible set; reason: the feasible set contains x = 0 and is bounded when c, d ≥ 0, so the supremum is attained and equals the maximum
--   - generalization: µ_ω are scenario probabilities → µ_ω ≥ 0, normalization not assumed; reason: the proofs use only µ_ω ≥ 0; probability weights are a special case
--   - generalization: supply nodes 1..m, demand nodes 1..n, a finite scenario set Ω → arbitrary finite types I, J, Ω (possibly empty); reason: the paper's index sets are an instance; with an empty index set F ≡ 0 and the statement stays true
--   - generalization: P a large constant bigger than p_ij for all (i,j) → p_ij ≤ P for all (i,j) (non-strict); reason: every step uses only P ≥ p_ij; a P strictly bigger than every p_ij satisfies the hypothesis
--   - reading: P a "large" constant → 0 ≤ P; reason: when some arc exists, P ≥ p_ij ≥ 0 already; the extra condition matters only when I or J is empty, where "bigger than every p_ij" bounds nothing and "large" is read as nonnegative (needed for ᾱ, β̄ ≥ 0 in (4))
--   - encoding: ℰ_max(𝒮) = max over 𝓕∖𝒮, undefined for 𝒮 = 𝓕 → ℰ_max(𝓕) = 0; reason: every ℰ_ij ≥ 0, so 0 is the supremum of the empty family in the nonnegative reals; only the undefined case is fixed
--   - generalization: ᾱ, β̄, ℰ computed from "an optimal solution" x^𝒮 → a run may use any optimal solution of each LP, chosen separately at every iteration; reason: this covers every heuristic of Algorithm 1 whatever optimal solutions it computes; a fixed choice per set is a special case
--   - encoding: "achieves an approximation factor of c" (Definition 1: within c times the optimal objective) → |A_K| ≤ K and c · F(B) ≤ F(A_K) for every B with |B| ≤ K; reason: OPT is the maximum of F over the finitely many B with |B| ≤ K, so the two forms are equivalent; |A_K| ≤ K records that the output is a solution of (FDP)
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §3.2, Proposition 2, p.15 (proof pp.15–16); Definition 1, p.7; Algorithm 1, p.15

import Mathlib
import Definitions.Def_CoverModular_FDPInstance_Standing
import Definitions.Def_CoverModular_FDPInstance_IsAlgorithm1Run

namespace CoverModular

variable {I J Ω : Type} [Fintype I] [Fintype J] [Fintype Ω] [DecidableEq I] [DecidableEq J]

/-- **Proposition 2** (DeValve, Pekeč, Wei, *Approximate submodularity in network design
problems*, SSRN 3844987, §3.2, Proposition 2, p.15). Any iterative heuristic that fits the
description of Algorithm 1 achieves an approximation factor of
`(1 − (1 − 2/K)^K)/2 ≥ (1 − e^{−2})/2`.

For every flexibility design instance satisfying the standing conditions, every budget
`K ≥ 1`, every constant `P` with `0 ≤ P` and `P ≥ p_ij` for all arcs, and every run
`𝒜_0, …, 𝒜_K` of Algorithm 1: the output `𝒜_K` has at most `K` arcs, it satisfies
`F(𝒜_K) ≥ ((1 − (1 − 2/K)^K)/2) F(𝒜)` for every structure `𝒜` with `|𝒜| ≤ K`, and
`(1 − (1 − 2/K)^K)/2 ≥ (1 − e^{−2})/2`.

**Formalization Note** "Approximation factor" (Definition 1, p.7) is stated against every
feasible structure of (FDP), which is equivalent to the bound against the optimum (a maximum
over the finitely many `𝒜` with `|𝒜| ≤ K`). A run may use any optimal LP solutions to compute
`ℰ` and may pick any arc satisfying line 4 (see `IsAlgorithm1Run`). -/
theorem proposition_2_greedy_type_approximation (inst : FDPInstance I J Ω)
    (hinst : inst.Standing) (K : ℕ) (hK : 1 ≤ K)
    (P : ℝ) (hP0 : 0 ≤ P) (hP : ∀ i j, inst.p i j ≤ P)
    (A : ℕ → Finset (I × J)) (hA : inst.IsAlgorithm1Run P K A) :
    (A K).card ≤ K ∧
      (∀ B : Finset (I × J), B.card ≤ K →
        (1 - (1 - 2 / (K : ℝ)) ^ K) / 2 * inst.F B ≤ inst.F (A K)) ∧
      (1 - Real.exp (-2)) / 2 ≤ (1 - (1 - 2 / (K : ℝ)) ^ K) / 2 := by sorry

end CoverModular
