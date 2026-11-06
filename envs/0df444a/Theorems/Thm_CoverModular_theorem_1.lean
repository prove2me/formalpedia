-- Prove2me | Theorems.Thm_CoverModular_theorem_1
-- name    : CoverModular.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:01.302954+00:00
-- url     : https://prove2.me/theorems/263da2b3-150a-4767-b917-1f6a8b86f7d6
-- title:
--   Theorem 1 — inequalities (7)–(8): the second-stage value $f$ is 2-cover modular
-- statement:
--   Fix one scenario ($c,d,p\ge0$) and a constant $P$ with $P\ge p_{ij}$ for all arcs. For any $\mathcal S,\mathcal T\subseteq\mathcal F$ and any optimal solution $x^{\mathcal S}$ of (3) for $\mathcal A=\mathcal S$, with $\bar\alpha^{\mathcal S},\bar\beta^{\mathcal S}$ the values (6),
--
--   $$
--   \begin{aligned}
--   f(\mathcal S\cup\mathcal T)&\le\sum_i c_i\bar\alpha^{\mathcal S}_i+\sum_j d_j\bar\beta^{\mathcal S}_j+\sum_{(i,j)\in\mathcal T\setminus\mathcal S}\min(c_i,d_j)\bigl(p_{ij}-\bar\alpha^{\mathcal S}_i-\bar\beta^{\mathcal S}_j\bigr)^+ &(7)\\
--   &\le 2f(\mathcal S)+\sum_{(i,j)\in\mathcal T\setminus\mathcal S}\bigl(f(\mathcal S\cup\{(i,j)\})-f(\mathcal S)\bigr). &(8)
--   \end{aligned}
--   $$
--
--   Thus the function $f$ is $2$-cover modular over $\mathcal F$.
--
--   This is the structural result of the paper: although $f$ is not submodular (Example 1), global changes are bounded by twice the current value plus the sum of local changes. Taking expectations, the same holds for the expected profit $F$, and it drives the approximation guarantee of Proposition 2.
--
--   Differences from the source:
--   - encoding: capacities c_i and demands d_j carry no printed sign → hypotheses c_i ≥ 0 and d_j ≥ 0; reason: they are capacities and demands; LP (3) is infeasible otherwise and display (6) splits only into > 0 and = 0, so only instances where f is undefined are excluded
--   - encoding: f(𝒜) = max of LP (3) → lpValue = sSup of the objective values over the feasible set; reason: the feasible set contains x = 0 and is bounded when c, d ≥ 0, so the supremum is attained and equals the maximum
--   - generalization: supply nodes 1..m and demand nodes 1..n → arbitrary finite types I, J (possibly empty); reason: the paper's index sets are an instance; with an empty index set every sum is empty and the statement stays true
--   - generalization: P a large constant bigger than p_ij for all (i,j) → p_ij ≤ P for all (i,j) (non-strict); reason: every step uses only P ≥ p_ij; a P strictly bigger than every p_ij satisfies the hypothesis
--   - reading: P a "large" constant → 0 ≤ P; reason: when some arc exists, P ≥ p_ij ≥ 0 already; the extra condition matters only when I or J is empty, where "bigger than every p_ij" bounds nothing and "large" is read as nonnegative (needed for ᾱ, β̄ ≥ 0 in (4))
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §3.1, Theorem 1, displays (7)–(8), p.12

import Mathlib
import Definitions.Def_CoverModular_IsOptimal
import Definitions.Def_CoverModular_alphaBar
import Definitions.Def_CoverModular_IsCoverModular

namespace CoverModular

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- **Theorem 1** (DeValve, Pekeč, Wei, *Approximate submodularity in network design problems*,
SSRN 3844987, §3.1, Theorem 1, displays (7)–(8), p.12). Fix one scenario and a constant `P`
with `0 ≤ P` and `p_ij ≤ P` for every arc. For any `𝒮, 𝒯 ⊆ 𝓕` and any optimal solution `x`
of (3) for `𝒜 = 𝒮` (defining `ᾱ^𝒮, β̄^𝒮` by (6)):

(7) `f(𝒮 ∪ 𝒯) ≤ ∑_i c_i ᾱ^𝒮_i + ∑_j d_j β̄^𝒮_j + ∑_{(i,j)∈𝒯\𝒮} min(c_i,d_j)(p_ij − ᾱ^𝒮_i − β̄^𝒮_j)^+`,

(8) and this is `≤ 2f(𝒮) + ∑_{(i,j)∈𝒯\𝒮} (f(𝒮 ∪ {(i,j)}) − f(𝒮))`.

Thus `f` is 2-cover modular over `𝓕`. -/
theorem theorem_1 (c : I → ℝ) (d : J → ℝ) (p : I → J → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ j, 0 ≤ d j) (hp : ∀ i j, 0 ≤ p i j)
    (P : ℝ) (hP0 : 0 ≤ P) (hP : ∀ i j, p i j ≤ P) :
    (∀ (S T : Finset (I × J)) (x : I → J → ℝ), IsOptimal c d p S x →
      lpValue c d p (S ∪ T) ≤
          ∑ i, c i * alphaBar c p P x i + ∑ j, d j * betaBar d p P x j +
            ∑ a ∈ T \ S, min (c a.1) (d a.2) *
              max (p a.1 a.2 - alphaBar c p P x a.1 - betaBar d p P x a.2) 0 ∧
        ∑ i, c i * alphaBar c p P x i + ∑ j, d j * betaBar d p P x j +
            ∑ a ∈ T \ S, min (c a.1) (d a.2) *
              max (p a.1 a.2 - alphaBar c p P x a.1 - betaBar d p P x a.2) 0 ≤
          2 * lpValue c d p S + ∑ a ∈ T \ S, (lpValue c d p (insert a S) - lpValue c d p S)) ∧
    IsCoverModular 2 (lpValue c d p) := by sorry

end CoverModular
