-- Prove2me | Theorems.Thm_FlexMargin_theorem_1
-- name    : FlexMargin.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:43:58.455033+00:00
-- url     : https://prove2.me/theorems/0f4f7590-504e-4380-8362-aae94f8ea6a2
-- title:
--   Theorem 1: representation of robust measures in $\Gamma$ (corrected: margins nonnegative)
-- statement:
--   Consider a system with $m$ plants of capacities $C\ge0$, $n$ products in categories $S_1,\dots,S_T$ with margins $0\le P_1<\dots<P_T$, and a design $\mathcal A$. Let $f(\mathcal A,d)=h\big(g(\mathcal A,d),\sum d_{s_1},\dots,\sum d_{s_T}\big)$ with $h(x,y_1,\dots,y_T)$ strictly increasing in $x$ for fixed $y$. Then for every $U$ part-wise independently symmetric around $\mu$, with $E=\{d-\mu:d\in U\}$,
--
--   $$
--   R^f(\mathcal A,U)=\min_{K\in Q,\ \varepsilon\in E}h\Big(\delta^K_\mu(\mathcal A)+\sum_{t=1}^T\sum_{r=0}^{t-1}\beta_{tr}\sum_{i=H_{tr}-k_{tr}+1}^{H_{tr}}\varepsilon_{s_t,i},\ \sum_{i\in s_1}(\mu_i+\varepsilon_i),\dots,\sum_{i\in s_T}(\mu_i+\varepsilon_i)\Big).
--   $$
--
--   Thus the worst case of every robust measure in $\Gamma$ depends on the design only through its DMGI values.
--
--   **Formalization Note** Both sides are infima in the extended reals.
--
--   Differences from the source:
--   - correction: no sign condition on the margins → ∀ t, 0 ≤ P t (margins nonnegative); reason: false with a negative margin: with h(x, y) = x it is Proposition 3, and false with a negative margin: T = 1, P_1 = −1, n = m = 1, A = {(a_1,b_1)}, C_1 = 1, µ = (1), U = {(1)} (part-wise symmetric around µ, E = {0}); g(A,d) = max{−x : 0 ≤ x ≤ 1} = 0 so R^g = 0, while K = (k_10 = 1) gives y = β_10 = −1, z = 0, δ = −1, so the right-hand side is min(−1, 0) = −1
--   - generalization: R^f(A,U) = min_{d∈U} f(A,d), with f continuous in d so that the minimum exists → R is the infimum in EReal over U (robustMeasure); no continuity of f, no compactness of U; reason: the EReal infimum equals the minimum whenever it exists, so the statement specializes to the source's
--   - generalization: min over K ∈ Q and ε ∈ E on the right-hand side → infimum in EReal over K ∈ Q and ε ∈ E; reason: equals the minimum whenever it exists; specializes to the source's identity
--   - reading: ε_{s_t,i}, the i-th entry of the residual vector of category S_t, order of s_t not fixed → entries of ε on S_t in increasing product index (Finset.orderEmbOfFin); reason: the source leaves the order of s_t unspecified; for part-wise symmetric sets the infimum does not depend on it
--   - reading: (4)/(5) list y_i + z_j ≥ p_i and the w-constraints, not z_j ≥ 0 → z ≥ 0 is a constraint of dmgi / dmgi5; reason: (4) is defined from dual feasibility of (3), which has z ≥ 0 (p. 17), and the proofs of Proposition 3 (p. 41) and Lemma 2 (p. 44) use it; without it a plant with no arcs makes (4) unbounded below
--   - encoding: capacities C_j (sign not stated) → hypothesis 0 ≤ C j; reason: with a negative capacity the LP (1) is infeasible and g is undefined; only excludes undefined cases
--   - encoding: plants a_1..a_m, products b_1..b_n, categories S_1..S_T (1-based), margins P_1 < ... < P_T → Fin m, Fin n, cat : Fin n → Fin T (0-based), P : Fin T → ℝ with StrictMono P, p_i = P (cat i); reason: Lean indexing; same instances
--   - encoding: parameter set K = {k_tr : t = 1..T, r = 0..t−1} and binary w_itr → K : (t : Fin T) → Fin (t+1) → ℕ (K t r is k_{t+1,r}); w as a level map w i ≤ cat i + 1; reason: Lean indexing; one level per product is exactly the w-constraints of (4)
--   - reading: Definition 2.2: E := {d − µ | d ∈ U} is part-wise independently symmetric, and Definition 2.1 is stated for sets ⊂ ℝ^n_+ → the sign condition is imposed on U only (IsPartwiseSymmAround); E satisfies clauses (1)–(2) of Definition 2.1 (IsPartwiseSymmCore) and may have negative entries; reason: E is the set of estimation errors around µ (p. 14), which fluctuate in both directions; applying ℝ^n_+ to E would force d ≥ µ on all of U. Every set admitted by the literal reading is admitted here, so the statement covers the source's
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §3.2, Theorem 1, p. 18

import Mathlib
import Definitions.Def_FlexMargin_marginMeasure
import Definitions.Def_FlexMargin_IsMonotonicInProfit
import Definitions.Def_FlexMargin_robustMeasure
import Definitions.Def_FlexMargin_IsPartwiseSymmAround
import Definitions.Def_FlexMargin_InQ
import Definitions.Def_FlexMargin_dmgi
import Definitions.Def_FlexMargin_residualTerm

open Finset

namespace FlexMargin

/-- **Theorem 1: representation of every robust measure in Γ (corrected: margins nonnegative).**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §3.2, Theorem 1, p. 18: "Let f be a deterministic measure function that is monotonic in profit
under fixed total demand in each product category Σdst and separable in Σdst for each 1 ≤ t ≤ T. Let
h(·) be the function such that h(x,y1,...,yT) is strictly increasing in x for fixed y1,...,yT, and
f(A,d) = h(g(A,d),Σds1,...,ΣdsT). Then for any uncertainty set U that is part-wise independently
symmetric around µ, we have Rf(A,U) = min_{K∈Q,ϵ∈E} h( δK_µ(A) + Σ_{t=1}^T ( Σ_{r=0}^{t−1} βtr
( Σ_{i=Htr−ktr+1}^{Htr} ϵst,i ) ), Σ_{i∈s1}(µi + ϵi), ..., Σ_{i∈sT}(µi + ϵi) )."

The general system of §2 (pp. 10–11): plants \`Fin m\` with capacities \`C ≥ 0\`, products \`Fin n\`,
margins \`P_1 < ⋯ < P_T\` (\`P : Fin T → ℝ\`, 0-based, \`StrictMono P\`) and categories \`cat : Fin n → Fin T\`
(product \`i\` has margin \`p_i = P (cat i)\`); a design \`A\` is any set of (plant, product) arcs.
`f = FlexMargin.marginMeasure C P cat h` with `h` strictly increasing in its first argument
(`FlexMargin.IsMonotonicInProfit`). For every `U` part-wise independently symmetric around `μ`, the
robust measure `R^f(A, U)` equals the infimum over `K ∈ Q` and `ε ∈ E = {d − μ | d ∈ U}` of `h` applied
to `δ^K_μ(A) + residual(K, ε)` and to the category totals `t ↦ Σ_{cat i = t} (μ_i + ε_i)`.

**Formalization Note.** (a) Correction: `∀ t, 0 ≤ P t` is added; with `h(x, y) = x` the counterexample
to Proposition 3 (`T = 1`, `P_1 = −1`, `U = {(1)}`: left side `0`, right side `−1`) applies. (b) Both sides
are `EReal` infima, equal to the paper's minima whenever those exist; `f` need not be continuous.
(c) `ε_{s_t,i}` lists `ε` on `S_t` in increasing product index. -/
theorem theorem_1 {m n T : ℕ} (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (P : Fin T → ℝ)
    (hP : StrictMono P) (hP0 : ∀ t, 0 ≤ P t) (cat : Fin n → Fin T)
    (h : ℝ → (Fin T → ℝ) → ℝ) (hh : IsMonotonicInProfit h) (μ : Fin n → ℝ)
    (A : Finset (Fin m × Fin n)) (U : Set (Fin n → ℝ)) (hU : IsPartwiseSymmAround cat μ U) :
    robustMeasure (marginMeasure C P cat h) A U =
      ⨅ (K : (t : Fin T) → Fin (t.val + 1) → ℕ) (_ : InQ cat K),
        ⨅ ε ∈ {e : Fin n → ℝ | ∃ d ∈ U, e = d - μ},
          ((h (dmgi C P cat μ A K + residualTerm P cat K ε)
            (fun t => ∑ i ∈ univ.filter (fun i => cat i = t), (μ i + ε i)) : ℝ) : EReal) := by sorry

end FlexMargin
