-- Prove2me | Theorems.Thm_CoverModular_display_9
-- name    : CoverModular.display_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:15:52.275601+00:00
-- url     : https://prove2.me/theorems/5c1400d3-19fd-4bf3-a852-18de950af22f
-- title:
--   Display (9) — the surrogate $\min(c_i,d_j)(p_{ij}-\bar\alpha^{\mathcal S}_i-\bar\beta^{\mathcal S}_j)^+$ is at most the marginal gain
-- statement:
--   Fix one scenario ($c,d,p\ge0$), a constant $P$ with $P\ge p_{ij}$ for all arcs, a set $\mathcal S\subseteq\mathcal F$, and an optimal solution $x^{\mathcal S}$ of (3) for $\mathcal A=\mathcal S$; let $\bar\alpha^{\mathcal S},\bar\beta^{\mathcal S}$ be the values (6). Then for **every** arc $(i,j)\in\mathcal F$,
--
--   $$
--   \min(c_i,d_j)\bigl(p_{ij}-\bar\alpha^{\mathcal S}_i-\bar\beta^{\mathcal S}_j\bigr)^+\le f(\mathcal S\cup\{(i,j)\})-f(\mathcal S).\tag{9}
--   $$
--
--   This is the key inequality in the proof of Theorem 1: it bounds the third summand of (7) by marginal gains, gives the dual feasibility of $(\bar\alpha^{\mathcal S},\bar\beta^{\mathcal S})$, and, after taking expectations, shows that $\mathcal E_{ij}(\mathcal S)$ is a lower bound on the marginal gain of $F$.
--
--   Differences from the source:
--   - encoding: capacities c_i and demands d_j carry no printed sign → hypotheses c_i ≥ 0 and d_j ≥ 0; reason: they are capacities and demands; LP (3) is infeasible otherwise and display (6) splits only into > 0 and = 0, so only instances where f is undefined are excluded
--   - encoding: f(𝒜) = max of LP (3) → lpValue = sSup of the objective values over the feasible set; reason: the feasible set contains x = 0 and is bounded when c, d ≥ 0, so the supremum is attained and equals the maximum
--   - generalization: supply nodes 1..m and demand nodes 1..n → arbitrary finite types I, J (possibly empty); reason: the paper's index sets are an instance; with an empty index set every sum is empty and the statement stays true
--   - generalization: P a large constant bigger than p_ij for all (i,j) → p_ij ≤ P for all (i,j) (non-strict); reason: every step uses only P ≥ p_ij; a P strictly bigger than every p_ij satisfies the hypothesis
--   - reading: P a "large" constant → 0 ≤ P; reason: when some arc exists, P ≥ p_ij ≥ 0 already; the extra condition matters only when I or J is empty, where "bigger than every p_ij" bounds nothing and "large" is read as nonnegative (needed for ᾱ, β̄ ≥ 0 in (4))
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §3.1, proof of Theorem 1, display (9), p.12

import Mathlib
import Definitions.Def_CoverModular_IsOptimal
import Definitions.Def_CoverModular_alphaBar

namespace CoverModular

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- **Display (9)** (DeValve, Pekeč, Wei, SSRN 3844987, §3.1, proof of Theorem 1, display (9),
p.12). Fix one scenario. Let `x` be an optimal solution of (3) for `𝒜 = 𝒮` and `P` a
constant with `P ≥ p_ij` for every arc. Then for **every** arc `(i, j) ∈ 𝓕`,
`min(c_i, d_j)(p_ij − ᾱ^𝒮_i − β̄^𝒮_j)^+ ≤ f(𝒮 ∪ {(i, j)}) − f(𝒮)`.

**Formalization Note** The paper's `P` is "a large constant bigger than `p_ij` for all
`(i, j)`"; here `0 ≤ P` and `p_ij ≤ P` for all arcs (non-strict). -/
theorem display_9 (c : I → ℝ) (d : J → ℝ) (p : I → J → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ j, 0 ≤ d j) (hp : ∀ i j, 0 ≤ p i j)
    (P : ℝ) (hP0 : 0 ≤ P) (hP : ∀ i j, p i j ≤ P)
    (S : Finset (I × J)) (x : I → J → ℝ) (hx : IsOptimal c d p S x) (i : I) (j : J) :
    min (c i) (d j) * max (p i j - alphaBar c p P x i - betaBar d p P x j) 0 ≤
      lpValue c d p (insert (i, j) S) - lpValue c d p S := by sorry

end CoverModular
