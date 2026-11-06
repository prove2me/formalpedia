-- Prove2me | Theorems.Thm_CoverModular_display_12
-- name    : CoverModular.display_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:15:49.609209+00:00
-- url     : https://prove2.me/theorems/35ce64da-dce3-4b8f-9e0d-d1cb840cff75
-- title:
--   Display (12) — $F(\mathcal S\cup\mathcal T)\le 2F(\mathcal S)+\sum_{(i,j)\in\mathcal T\setminus\mathcal S}\mathcal E_{ij}(\mathcal S)$
-- statement:
--   For a flexibility design instance satisfying the standing conditions, a constant $P$ with $P\ge p_{ij}$ for all arcs, sets $\mathcal S,\mathcal T\subseteq\mathcal F$, and optimal solutions $x^{\mathcal S}_\omega$ of the LP for $\mathcal S$ in every scenario $\omega$ (which define the surrogates $\mathcal E_{ij}(\mathcal S)$ of (11)),
--
--   $$
--   F(\mathcal S\cup\mathcal T)\le 2F(\mathcal S)+\sum_{(i,j)\in\mathcal T\setminus\mathcal S}\mathcal E_{ij}(\mathcal S).\tag{12}
--   $$
--
--   It is the expectation of inequality (7) of Theorem 1, combined with $\sum_i c_{i\omega}\bar\alpha^{\mathcal S}_{i\omega}+\sum_j d_{j\omega}\bar\beta^{\mathcal S}_{j\omega}=2f(\mathcal S,\omega)$.
--
--   Differences from the source:
--   - encoding: capacities c_iω and demands d_jω carry no printed sign → c_iω ≥ 0 and d_jω ≥ 0 (in FDPInstance.Standing); reason: they are capacities and demands; LP (1) is infeasible otherwise and display (6) splits only into > 0 and = 0, so only instances where F is undefined are excluded
--   - encoding: f(𝒜, ω) = max of LP (1) → lpValue = sSup of the objective values over the feasible set; reason: the feasible set contains x = 0 and is bounded when c, d ≥ 0, so the supremum is attained and equals the maximum
--   - generalization: µ_ω are scenario probabilities → µ_ω ≥ 0, normalization not assumed; reason: the proofs use only µ_ω ≥ 0; probability weights are a special case
--   - generalization: supply nodes 1..m, demand nodes 1..n, a finite scenario set Ω → arbitrary finite types I, J, Ω (possibly empty); reason: the paper's index sets are an instance; with an empty index set F ≡ 0 and the statement stays true
--   - generalization: P a large constant bigger than p_ij for all (i,j) → p_ij ≤ P for all (i,j) (non-strict); reason: every step uses only P ≥ p_ij; a P strictly bigger than every p_ij satisfies the hypothesis
--   - reading: P a "large" constant → 0 ≤ P; reason: when some arc exists, P ≥ p_ij ≥ 0 already; the extra condition matters only when I or J is empty, where "bigger than every p_ij" bounds nothing and "large" is read as nonnegative (needed for ᾱ, β̄ ≥ 0 in (4))
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §3.2, proof of Proposition 2, display (12), p.15

import Mathlib
import Definitions.Def_CoverModular_IsOptimal
import Definitions.Def_CoverModular_FDPInstance_Standing
import Definitions.Def_CoverModular_FDPInstance_F
import Definitions.Def_CoverModular_FDPInstance_E

namespace CoverModular

variable {I J Ω : Type} [Fintype I] [Fintype J] [Fintype Ω] [DecidableEq I] [DecidableEq J]

/-- **Display (12)** (DeValve, Pekeč, Wei, SSRN 3844987, §3.2, proof of Proposition 2, display
(12), p.15). Under the standing conditions, for a constant `P` with `0 ≤ P`, `p_ij ≤ P`, any
`𝒮, 𝒯 ⊆ 𝓕`, and optimal solutions `x ω` of the LP for `𝒮` in every scenario `ω` (which
define `ℰ_ij(𝒮)` by (11)), `F(𝒮 ∪ 𝒯) ≤ 2F(𝒮) + ∑_{(i,j)∈𝒯\𝒮} ℰ_ij(𝒮)`. -/
theorem display_12 (inst : FDPInstance I J Ω) (hinst : inst.Standing)
    (P : ℝ) (hP0 : 0 ≤ P) (hP : ∀ i j, inst.p i j ≤ P)
    (S T : Finset (I × J)) (x : Ω → I → J → ℝ)
    (hx : ∀ ω, IsOptimal (fun i => inst.c i ω) (fun j => inst.d j ω) inst.p S (x ω)) :
    inst.F (S ∪ T) ≤ 2 * inst.F S + ∑ a ∈ T \ S, inst.E P x a.1 a.2 := by sorry

end CoverModular
