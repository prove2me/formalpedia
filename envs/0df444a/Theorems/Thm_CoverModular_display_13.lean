-- Prove2me | Theorems.Thm_CoverModular_display_13
-- name    : CoverModular.display_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:53.154807+00:00
-- url     : https://prove2.me/theorems/a3a9ac5f-5863-40ce-9b7e-269a9ca71e3e
-- title:
--   Display (13) — $F(\mathcal A^*)\le F(\mathcal S\cup\mathcal A^*)\le 2F(\mathcal S)+\sum\mathcal E_{ij}(\mathcal S)\le 2F(\mathcal S)+K\mathcal E_{\max}(\mathcal S)$
-- statement:
--   For a flexibility design instance satisfying the standing conditions, a constant $P$ with $P\ge p_{ij}$ for all arcs, a budget $K$, any structure $\mathcal A^*$ with $|\mathcal A^*|\le K$, any structure $\mathcal S$ (the iterate $\mathcal A_{t-1}$ of the paper), and optimal solutions $x^{\mathcal S}_\omega$ of the LP for $\mathcal S$ in every scenario,
--
--   $$
--   F(\mathcal A^*)\le F(\mathcal S\cup\mathcal A^*)\le 2F(\mathcal S)+\sum_{(i,j)\in\mathcal A^*\setminus\mathcal S}\mathcal E_{ij}(\mathcal S)\le 2F(\mathcal S)+K\,\mathcal E_{\max}(\mathcal S).\tag{13}
--   $$
--
--   The three inequalities are stated as a conjunction. The first is monotonicity (Lemma 2), the second is (12), and the third uses $|\mathcal A^*\setminus\mathcal S|\le K$.
--
--   Differences from the source:
--   - encoding: capacities c_iω and demands d_jω carry no printed sign → c_iω ≥ 0 and d_jω ≥ 0 (in FDPInstance.Standing); reason: they are capacities and demands; LP (1) is infeasible otherwise and display (6) splits only into > 0 and = 0, so only instances where F is undefined are excluded
--   - encoding: f(𝒜, ω) = max of LP (1) → lpValue = sSup of the objective values over the feasible set; reason: the feasible set contains x = 0 and is bounded when c, d ≥ 0, so the supremum is attained and equals the maximum
--   - generalization: µ_ω are scenario probabilities → µ_ω ≥ 0, normalization not assumed; reason: the proofs use only µ_ω ≥ 0; probability weights are a special case
--   - generalization: supply nodes 1..m, demand nodes 1..n, a finite scenario set Ω → arbitrary finite types I, J, Ω (possibly empty); reason: the paper's index sets are an instance; with an empty index set F ≡ 0 and the statement stays true
--   - generalization: P a large constant bigger than p_ij for all (i,j) → p_ij ≤ P for all (i,j) (non-strict); reason: every step uses only P ≥ p_ij; a P strictly bigger than every p_ij satisfies the hypothesis
--   - reading: P a "large" constant → 0 ≤ P; reason: when some arc exists, P ≥ p_ij ≥ 0 already; the extra condition matters only when I or J is empty, where "bigger than every p_ij" bounds nothing and "large" is read as nonnegative (needed for ᾱ, β̄ ≥ 0 in (4))
--   - encoding: ℰ_max(𝒮) = max over 𝓕∖𝒮, undefined for 𝒮 = 𝓕 → ℰ_max(𝓕) = 0; reason: every ℰ_ij ≥ 0, so 0 is the supremum of the empty family in the nonnegative reals; only the undefined case is fixed
--   - generalization: 𝒜* the optimal solution of (FDP) and 𝒜_{t−1} an iterate of Algorithm 1 → every 𝒜* with |𝒜*| ≤ K and every set 𝒮 with optimal LP solutions; reason: the chain uses only |𝒜*| ≤ K and the optimality of the LP solutions; the paper's sets are instances
--   - generalization: the budget K a positive integer (Proposition 2 uses 2/K) → any natural number K, including K = 0; reason: the chain uses only |𝒜*| ≤ K and K ≥ 0; every positive K is an instance (at K = 0, 𝒜* = ∅ and the chain still holds)
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §3.2, proof of Proposition 2, display (13), p.15

import Mathlib
import Definitions.Def_CoverModular_IsOptimal
import Definitions.Def_CoverModular_FDPInstance_Standing
import Definitions.Def_CoverModular_FDPInstance_F
import Definitions.Def_CoverModular_FDPInstance_Emax

namespace CoverModular

variable {I J Ω : Type} [Fintype I] [Fintype J] [Fintype Ω] [DecidableEq I] [DecidableEq J]

/-- **Display (13)** (DeValve, Pekeč, Wei, SSRN 3844987, §3.2, proof of Proposition 2, display
(13), p.15). Under the standing conditions, for a constant `P` with `0 ≤ P`, `p_ij ≤ P`, a
budget `K`, any `𝒜* ⊆ 𝓕` with `|𝒜*| ≤ K`, any `𝒮 ⊆ 𝓕` (the paper's `𝒜_{t−1}`), and optimal
solutions `x ω` of the LP for `𝒮` in every scenario,
`F(𝒜*) ≤ F(𝒮 ∪ 𝒜*) ≤ 2F(𝒮) + ∑_{(i,j)∈𝒜*\𝒮} ℰ_ij(𝒮) ≤ 2F(𝒮) + K ℰ_max(𝒮)`.

**Formalization Note** The page states this for the optimal solution `𝒜*` of (FDP) and the
iterate `𝒜_{t−1}` of a run; the chain uses only `|𝒜*| ≤ K`, so it is stated for every such
`𝒜*` and every set `𝒮`. -/
theorem display_13 (inst : FDPInstance I J Ω) (hinst : inst.Standing)
    (P : ℝ) (hP0 : 0 ≤ P) (hP : ∀ i j, inst.p i j ≤ P) (K : ℕ)
    (B : Finset (I × J)) (hB : B.card ≤ K) (S : Finset (I × J)) (x : Ω → I → J → ℝ)
    (hx : ∀ ω, IsOptimal (fun i => inst.c i ω) (fun j => inst.d j ω) inst.p S (x ω)) :
    inst.F B ≤ inst.F (S ∪ B) ∧
      inst.F (S ∪ B) ≤ 2 * inst.F S + ∑ a ∈ B \ S, inst.E P x a.1 a.2 ∧
      2 * inst.F S + ∑ a ∈ B \ S, inst.E P x a.1 a.2 ≤ 2 * inst.F S + K * inst.Emax P x S := by sorry

end CoverModular
