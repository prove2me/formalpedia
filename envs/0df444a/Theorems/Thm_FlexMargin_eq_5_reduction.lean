-- Prove2me | Theorems.Thm_FlexMargin_eq_5_reduction
-- name    : FlexMargin.eq_5_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:45:52.708528+00:00
-- url     : https://prove2.me/theorems/dd838f5b-fdfc-4f97-abd2-c78c25019c12
-- title:
--   Reduction of (4) to (5) for a constant mean demand
-- statement:
--   Suppose all capacities are $1$ and the mean demand is constant, $\mu_i=c$ for all $i$. Then for every design $\mathcal A$ and every $K\in Q$, the term $\sum_i\mu_i y_i$ of (4) equals the constant $c\sum_t\sum_{r<t}k_{tr}\beta_{tr}$ on the feasible set, so
--
--   $$
--   \delta^K_\mu(\mathcal A)=c\sum_{t=1}^T\sum_{r=0}^{t-1}k_{tr}\beta_{tr}+\delta^K(\mathcal A),
--   $$
--
--   where $\delta^K(\mathcal A)$ is the optimal value of (5). Hence comparing (5) for two designs is the same as comparing (4).
--
--   Differences from the source:
--   - generalization: §4 setting: n plants, n products, two categories → any numbers m of plants, n of products and T of categories, unit capacities; reason: the argument is the same; with m = n and T = 2 the statement is the page's
--   - encoding: the term Σ µ_i y_i is a constant and may be omitted → the constant c Σ_t Σ_{r<t} k_tr β_tr is written out; reason: products at their own level r = t contribute β_tt = 0
--   - reading: (4)/(5) list y_i + z_j ≥ p_i and the w-constraints, not z_j ≥ 0 → z ≥ 0 is a constraint of dmgi / dmgi5; reason: (4) is defined from dual feasibility of (3), which has z ≥ 0 (p. 17), and the proofs of Proposition 3 (p. 41) and Lemma 2 (p. 44) use it; without it a plant with no arcs makes (4) unbounded below
--   - encoding: plants a_1..a_m, products b_1..b_n, categories S_1..S_T (1-based), margins P_1 < ... < P_T → Fin m, Fin n, cat : Fin n → Fin T (0-based), P : Fin T → ℝ with StrictMono P, p_i = P (cat i); reason: Lean indexing; same instances
--   - encoding: parameter set K = {k_tr : t = 1..T, r = 0..t−1} and binary w_itr → K : (t : Fin T) → Fin (t+1) → ℕ (K t r is k_{t+1,r}); w as a level map w i ≤ cat i + 1; reason: Lean indexing; one level per product is exactly the w-constraints of (4)
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §4, p. 20 (unnumbered, display (5))

import Mathlib
import Definitions.Def_FlexMargin_InQ
import Definitions.Def_FlexMargin_betaCoef
import Definitions.Def_FlexMargin_dmgi
import Definitions.Def_FlexMargin_dmgi5

namespace FlexMargin

/-- **The reduction of (4) to (5) for a constant mean demand.**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §4, p. 20 (unnumbered, display (5)): "When µi = µj for all 1 ≤ i,j ≤ n, the term Σ_{i=1}^n µiyi
in the objective function (4) is a constant for any fixed parameter set K. Therefore, we may omit this
term without loss of optimality and the DMGI for a homogeneous design A, denoted by δK(A), is
equivalent to the optimal objective function of the following problem:" (5).

For unit capacities (`C ≡ 1`, §4), a constant mean demand `μ ≡ c`, any margins `P`, categories `cat`,
design `A` and `K ∈ Q`: `δ^K_μ(A)` of (4) (`FlexMargin.dmgi`) equals the constant
`c · Σ_t Σ_{r<t} k_{tr} β_{tr}` plus `δ^K(A)` of (5) (`FlexMargin.dmgi5`).

**Formalization Note.** (a) The constant `Σ_i μ_i y_i = c Σ_t Σ_{r<t} k_{tr} β_{tr}` is made explicit
(the `|S_t| − Σ_r k_{tr}` products at the own level have `β_{tt} = 0`). (b) Stated for any numbers of
plants, products and categories (the page is in the §4 setting `m = n`, `T = 2`), which specializes to
the page's claim. (c) `K ∈ Q` is required: outside `Q` both programs are infeasible. -/
theorem eq_5_reduction {m n T : ℕ} (P : Fin T → ℝ) (hP : StrictMono P) (cat : Fin n → Fin T)
    (A : Finset (Fin m × Fin n)) (K : (t : Fin T) → Fin (t.val + 1) → ℕ) (hK : InQ cat K)
    (c : ℝ) :
    dmgi (fun _ => (1 : ℝ)) P cat (fun _ => c) A K =
      c * ∑ t : Fin T, ∑ r : Fin (t.val + 1), (K t r : ℝ) * betaCoef P t r.val +
        dmgi5 P cat A K := by sorry

end FlexMargin
