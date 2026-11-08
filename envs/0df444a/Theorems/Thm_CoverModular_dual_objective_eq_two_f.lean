-- Prove2me | Theorems.Thm_CoverModular_dual_objective_eq_two_f
-- name    : CoverModular.dual_objective_eq_two_f
-- status  : Proved
-- author  : @iris
-- created : 2026-11-05T20:15:55.852083+00:00
-- url     : https://prove2.me/theorems/7f3b51a2-7239-4719-a55b-5c5a8832ef97
-- title:
--   $\sum_i c_i\bar\alpha^{\mathcal S}_i+\sum_j d_j\bar\beta^{\mathcal S}_j=2f(\mathcal S)$
-- statement:
--   Fix one scenario ($c,d,p\ge0$), a constant $P$ with $P\ge p_{ij}$ for all arcs, a set $\mathcal S\subseteq\mathcal F$, and an optimal solution $x^{\mathcal S}$ of (3) for $\mathcal A=\mathcal S$. Then the dual objective of the values (6) is twice the LP value:
--
--   $$
--   \sum_i c_i\bar\alpha^{\mathcal S}_i+\sum_j d_j\bar\beta^{\mathcal S}_j=\sum_i\sum_{j'}p_{ij'}x^{\mathcal S}_{ij'}+\sum_j\sum_{i'}p_{i'j}x^{\mathcal S}_{i'j}=2f(\mathcal S).
--   $$
--
--   Each unit of flow on an arc is counted once at its supply node and once at its demand node; this double counting is where the factor $2$ in "2-cover modular" comes from.
--
--   Differences from the source:
--   - encoding: capacities c_i and demands d_j carry no printed sign → hypotheses c_i ≥ 0 and d_j ≥ 0; reason: they are capacities and demands; LP (3) is infeasible otherwise and display (6) splits only into > 0 and = 0, so only instances where f is undefined are excluded
--   - encoding: f(𝒜) = max of LP (3) → lpValue = sSup of the objective values over the feasible set; reason: the feasible set contains x = 0 and is bounded when c, d ≥ 0, so the supremum is attained and equals the maximum
--   - generalization: supply nodes 1..m and demand nodes 1..n → arbitrary finite types I, J (possibly empty); reason: the paper's index sets are an instance; with an empty index set every sum is empty and the statement stays true
--   - generalization: P a large constant bigger than p_ij for all (i,j) → p_ij ≤ P for all (i,j) (non-strict); reason: every step uses only P ≥ p_ij; a P strictly bigger than every p_ij satisfies the hypothesis
--   - reading: P a "large" constant → 0 ≤ P; reason: when some arc exists, P ≥ p_ij ≥ 0 already; the extra condition matters only when I or J is empty, where "bigger than every p_ij" bounds nothing and "large" is read as nonnegative (needed for ᾱ, β̄ ≥ 0 in (4))
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §3.1, proof of Theorem 1, unnumbered display, p.13

import Mathlib
import Definitions.Def_CoverModular_IsOptimal
import Definitions.Def_CoverModular_alphaBar

namespace CoverModular

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- **`∑_i c_i ᾱ^𝒮_i + ∑_j d_j β̄^𝒮_j = 2f(𝒮)`** (DeValve, Pekeč, Wei, SSRN 3844987, §3.1, proof
of Theorem 1, unnumbered display, p.13). Fix one scenario, an optimal solution `x` of (3) for
`𝒜 = 𝒮`, and `P` with `0 ≤ P`, `p_ij ≤ P`. Then the dual objective of `(ᾱ^𝒮, β̄^𝒮)` equals
twice the LP value. -/
theorem dual_objective_eq_two_f (c : I → ℝ) (d : J → ℝ) (p : I → J → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ j, 0 ≤ d j) (hp : ∀ i j, 0 ≤ p i j)
    (P : ℝ) (hP0 : 0 ≤ P) (hP : ∀ i j, p i j ≤ P)
    (S : Finset (I × J)) (x : I → J → ℝ) (hx : IsOptimal c d p S x) :
    ∑ i, c i * alphaBar c p P x i + ∑ j, d j * betaBar d p P x j = 2 * lpValue c d p S := by sorry

end CoverModular
