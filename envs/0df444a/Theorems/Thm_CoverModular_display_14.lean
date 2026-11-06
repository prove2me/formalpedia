-- Prove2me | Theorems.Thm_CoverModular_display_14
-- name    : CoverModular.display_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:36.219686+00:00
-- url     : https://prove2.me/theorems/a255b270-dc03-4735-bd79-0c3001d99cb5
-- title:
--   Display (14) — $F(\mathcal A^*)\le 2\sum_{\tau=1}^{t-1}\rho_\tau+K\rho_t$ along a run of Algorithm 1
-- statement:
--   For a flexibility design instance satisfying the standing conditions, a constant $P$ with $P\ge p_{ij}$ for all arcs, a run $\mathcal A_0,\dots,\mathcal A_K$ of Algorithm 1 and any structure $\mathcal A^*$ with $|\mathcal A^*|\le K$, write $\rho_t=F(\mathcal A_t)-F(\mathcal A_{t-1})$. Then for each $t=1,\dots,K$, with $\mathcal E_{\max}(\mathcal A_{t-1})$ computed from the optimal LP solutions the run uses at iteration $t$,
--
--   $$
--   F(\mathcal A^*)\le 2F(\mathcal A_{t-1})+K\,\mathcal E_{\max}(\mathcal A_{t-1})\le 2F(\mathcal A_{t-1})+K\rho_t=2\sum_{\tau=1}^{t-1}\rho_\tau+K\rho_t.\tag{14}
--   $$
--
--   The chain is stated as a conjunction of its two inequalities and its equality; the equality is the telescoping $F(\mathcal A_{t-1})=\sum_{\tau=1}^{t-1}\rho_\tau$ (using $F(\mathcal A_0)=F(\emptyset)$, which the paper takes as $0$).
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
--   - generalization: 𝒜* the optimal solution of (FDP) → every 𝒜* with |𝒜*| ≤ K; reason: the chain uses only |𝒜*| ≤ K; the optimum is one such set
--   - generalization: the budget K a positive integer (Proposition 2 uses 2/K) → any natural number K, including K = 0; reason: every positive K is an instance; at K = 0 there is no iteration t ∈ {1, …, K} and the statement holds vacuously
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §3.2, proof of Proposition 2, display (14), p.16

import Mathlib
import Definitions.Def_CoverModular_FDPInstance_Standing
import Definitions.Def_CoverModular_FDPInstance_IsAlgorithm1Run

namespace CoverModular

variable {I J Ω : Type} [Fintype I] [Fintype J] [Fintype Ω] [DecidableEq I] [DecidableEq J]

/-- **Display (14)** (DeValve, Pekeč, Wei, SSRN 3844987, §3.2, proof of Proposition 2, display
(14), p.16). Under the standing conditions, let `P` satisfy `0 ≤ P`, `p_ij ≤ P`, let
`𝒜_0, …, 𝒜_K` be a run of Algorithm 1 with budget `K`, let `𝒜* ⊆ 𝓕` with `|𝒜*| ≤ K`, and
write `ρ_t = F(𝒜_t) − F(𝒜_{t−1})`. Then for each `t = 1, …, K`, with the optimal solutions
`x` the run uses at step `t` (defining `ℰ_max(𝒜_{t−1})`),
`F(𝒜*) ≤ 2F(𝒜_{t−1}) + Kℰ_max(𝒜_{t−1}) ≤ 2F(𝒜_{t−1}) + Kρ_t = 2∑_{τ=1}^{t−1} ρ_τ + Kρ_t`.

**Formalization Note** The page's `𝒜*` is the optimal solution of (FDP); the inequality is
stated for every `𝒜*` with `|𝒜*| ≤ K`. The optimal solutions behind `ℰ_max(𝒜_{t−1})` are
existentially quantified, as in `IsAlgorithm1Run`. -/
theorem display_14 (inst : FDPInstance I J Ω) (hinst : inst.Standing)
    (P : ℝ) (hP0 : 0 ≤ P) (hP : ∀ i j, inst.p i j ≤ P) (K : ℕ)
    (A : ℕ → Finset (I × J)) (hA : inst.IsAlgorithm1Run P K A)
    (B : Finset (I × J)) (hB : B.card ≤ K) :
    ∀ t ∈ Finset.Icc 1 K, ∃ x : Ω → I → J → ℝ,
      (∀ ω, IsOptimal (fun i => inst.c i ω) (fun j => inst.d j ω) inst.p (A (t - 1)) (x ω)) ∧
      inst.F B ≤ 2 * inst.F (A (t - 1)) + K * inst.Emax P x (A (t - 1)) ∧
      2 * inst.F (A (t - 1)) + K * inst.Emax P x (A (t - 1)) ≤
        2 * inst.F (A (t - 1)) + K * (inst.F (A t) - inst.F (A (t - 1))) ∧
      2 * inst.F (A (t - 1)) + K * (inst.F (A t) - inst.F (A (t - 1))) =
        2 * ∑ τ ∈ Finset.Icc 1 (t - 1), (inst.F (A τ) - inst.F (A (τ - 1))) +
          K * (inst.F (A t) - inst.F (A (t - 1))) := by sorry

end CoverModular
