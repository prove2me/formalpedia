-- Prove2me | Theorems.Thm_CoverModular_dual_feasible_alphaBar_betaBar
-- name    : CoverModular.dual_feasible_alphaBar_betaBar
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:15:47.90302+00:00
-- url     : https://prove2.me/theorems/148c47a5-0ccd-4eaf-9823-9d3bf25e8452
-- title:
--   $(\bar\alpha^{\mathcal S},\bar\beta^{\mathcal S})$ is feasible for the dual (4) with $\mathcal A=\mathcal S$
-- statement:
--   Fix one scenario ($c,d,p\ge0$), a constant $P$ with $P\ge p_{ij}$ for all arcs, a set $\mathcal S\subseteq\mathcal F$, and an optimal solution $x^{\mathcal S}$ of (3) for $\mathcal A=\mathcal S$. Then the values (6) satisfy
--
--   $$
--   \bar\alpha^{\mathcal S}_i+\bar\beta^{\mathcal S}_j\ge p_{ij}\quad\text{for all }(i,j)\in\mathcal S,\qquad \bar\alpha^{\mathcal S}_i\ge0,\quad\bar\beta^{\mathcal S}_j\ge0 ,
--   $$
--
--   that is, $(\bar\alpha^{\mathcal S},\bar\beta^{\mathcal S})$ is a feasible solution of the dual (4) for $\mathcal A=\mathcal S$. Combined with Lemma 1 this gives inequality (7).
--
--   Differences from the source:
--   - encoding: capacities c_i and demands d_j carry no printed sign → hypotheses c_i ≥ 0 and d_j ≥ 0; reason: they are capacities and demands; LP (3) is infeasible otherwise and display (6) splits only into > 0 and = 0, so only instances where f is undefined are excluded
--   - generalization: supply nodes 1..m and demand nodes 1..n → arbitrary finite types I, J (possibly empty); reason: the paper's index sets are an instance; with an empty index set every sum is empty and the statement stays true
--   - generalization: P a large constant bigger than p_ij for all (i,j) → p_ij ≤ P for all (i,j) (non-strict); reason: every step uses only P ≥ p_ij; a P strictly bigger than every p_ij satisfies the hypothesis
--   - reading: P a "large" constant → 0 ≤ P; reason: when some arc exists, P ≥ p_ij ≥ 0 already; the extra condition matters only when I or J is empty, where "bigger than every p_ij" bounds nothing and "large" is read as nonnegative (needed for ᾱ, β̄ ≥ 0 in (4))
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §3.1, proof of Theorem 1, p.12

import Mathlib
import Definitions.Def_CoverModular_IsOptimal
import Definitions.Def_CoverModular_IsDualFeasible
import Definitions.Def_CoverModular_alphaBar

namespace CoverModular

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- **Dual feasibility of `(ᾱ^𝒮, β̄^𝒮)`** (DeValve, Pekeč, Wei, SSRN 3844987, §3.1, proof of
Theorem 1, p.12: "ᾱ^𝒮_i + β̄^𝒮_j ≥ p_ij for all (i, j) ∈ 𝒮, implying that ᾱ^𝒮 and β̄^𝒮 is a
feasible dual solution to (4) for 𝒜 = 𝒮"). Fix one scenario, an optimal solution `x` of (3)
for `𝒜 = 𝒮`, and `P` with `0 ≤ P`, `p_ij ≤ P`. Then `(ᾱ^𝒮, β̄^𝒮)` of (6) is feasible for
(4) with `𝒜 = 𝒮` (including the sign constraints `ᾱ, β̄ ≥ 0`). -/
theorem dual_feasible_alphaBar_betaBar (c : I → ℝ) (d : J → ℝ) (p : I → J → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ j, 0 ≤ d j) (hp : ∀ i j, 0 ≤ p i j)
    (P : ℝ) (hP0 : 0 ≤ P) (hP : ∀ i j, p i j ≤ P)
    (S : Finset (I × J)) (x : I → J → ℝ) (hx : IsOptimal c d p S x) :
    IsDualFeasible p S (alphaBar c p P x) (betaBar d p P x) := by sorry

end CoverModular
