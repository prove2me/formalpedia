-- Prove2me | Theorems.Thm_CoverModular_lemma_2
-- name    : CoverModular.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:15:38.234071+00:00
-- url     : https://prove2.me/theorems/26181f5d-6b28-468a-adad-0d2b5b0f1e3c
-- title:
--   Lemma 2 — the expected profit $F$ is non-negative and monotone
-- statement:
--   For a flexibility design instance satisfying the standing conditions ($\mu_\omega,c_{i\omega},d_{j\omega},p_{ij}\ge0$), the expected profit $F:2^{\mathcal F}\to\mathbb R$ is
--
--   1. non-negative: $F(\mathcal A)\ge0$ for every $\mathcal A\subseteq\mathcal F$;
--   2. monotone: $F(\mathcal A)\le F(\mathcal B)$ whenever $\mathcal A\subseteq\mathcal B\subseteq\mathcal F$.
--
--   Together with 2-cover modularity these are the properties of $F$ used in the analysis of greedy-type heuristics.
--
--   Differences from the source:
--   - encoding: capacities c_iω and demands d_jω carry no printed sign → c_iω ≥ 0 and d_jω ≥ 0 (in FDPInstance.Standing); reason: they are capacities and demands; LP (1) is infeasible otherwise and display (6) splits only into > 0 and = 0, so only instances where F is undefined are excluded
--   - encoding: f(𝒜, ω) = max of LP (1) → lpValue = sSup of the objective values over the feasible set; reason: the feasible set contains x = 0 and is bounded when c, d ≥ 0, so the supremum is attained and equals the maximum
--   - generalization: µ_ω are scenario probabilities → µ_ω ≥ 0, normalization not assumed; reason: the proofs use only µ_ω ≥ 0; probability weights are a special case
--   - generalization: supply nodes 1..m, demand nodes 1..n, a finite scenario set Ω → arbitrary finite types I, J, Ω (possibly empty); reason: the paper's index sets are an instance; with an empty index set F ≡ 0 and the statement stays true
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §3.2, Lemma 2, p.15

import Mathlib
import Definitions.Def_CoverModular_FDPInstance_Standing
import Definitions.Def_CoverModular_FDPInstance_F

namespace CoverModular

variable {I J Ω : Type} [Fintype I] [Fintype J] [Fintype Ω] [DecidableEq I] [DecidableEq J]

/-- **Lemma 2** (DeValve, Pekeč, Wei, SSRN 3844987, §3.2, Lemma 2, p.15). Under the standing
conditions, the expected profit `F : 2^𝓕 → ℝ` is non-negative and monotone. -/
theorem lemma_2 (inst : FDPInstance I J Ω) (hinst : inst.Standing) :
    (∀ A : Finset (I × J), 0 ≤ inst.F A) ∧
      ∀ A B : Finset (I × J), A ⊆ B → inst.F A ≤ inst.F B := by sorry

end CoverModular
