-- Prove2me | Theorems.Thm_FlexMargin_proposition_3
-- name    : FlexMargin.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:43:15.831753+00:00
-- url     : https://prove2.me/theorems/4e642d84-d5ef-4c06-be2b-f08fa3670f17
-- title:
--   Proposition 3: worst-case profit through the DMGI (corrected: margins nonnegative)
-- statement:
--   Consider a system with $m$ plants of capacities $C\ge0$, $n$ products in categories $S_1,\dots,S_T$ with margins $0\le P_1<\dots<P_T$, and a design $\mathcal A$. Let $U$ be part-wise independently symmetric around $\mu$ and $E=\{d-\mu:d\in U\}$. Then the worst-case profit is
--
--   $$
--   R^g(\mathcal A,U)=\min_{K\in Q,\ \varepsilon\in E}\Big\{\delta^K_\mu(\mathcal A)+\sum_{t=1}^T\sum_{r=0}^{t-1}\beta_{tr}\sum_{i=H_{tr}-k_{tr}+1}^{H_{tr}}\varepsilon_{s_t,i}\Big\}, \tag{7}
--   $$
--
--   where $\varepsilon_{s_t}$ is the residual vector on category $S_t$ and $H_{tr}=\sum_{j\le r}k_{tj}$. It is the special case $h(x,y)=x$ of Theorem 1 and the first step of its proof.
--
--   **Formalization Note** Both sides are infima in the extended reals.
--
--   Differences from the source:
--   - correction: no sign condition on the margins → ∀ t, 0 ≤ P t (margins nonnegative); reason: false with a negative margin: T = 1, P_1 = −1, n = m = 1, A = {(a_1,b_1)}, C_1 = 1, µ = (1), U = {(1)} (part-wise symmetric around µ, E = {0}); g(A,d) = max{−x : 0 ≤ x ≤ 1} = 0 so R^g = 0, while K = (k_10 = 1) gives y = β_10 = −1, z = 0, δ = −1, so the right-hand side is min(−1, 0) = −1
--   - generalization: R^f(A,U) = min_{d∈U} f(A,d), with f continuous in d so that the minimum exists → R is the infimum in EReal over U (robustMeasure); no continuity of f, no compactness of U; reason: the EReal infimum equals the minimum whenever it exists, so the statement specializes to the source's
--   - generalization: min over K ∈ Q and ε ∈ E on the right-hand side → infimum in EReal over K ∈ Q and ε ∈ E; reason: equals the minimum whenever it exists; specializes to the source's identity
--   - reading: ε_{s_t,i}, the i-th entry of the residual vector of category S_t, order of s_t not fixed → entries of ε on S_t in increasing product index (Finset.orderEmbOfFin); reason: the source leaves the order of s_t unspecified; for part-wise symmetric sets the infimum does not depend on it
--   - reading: (4)/(5) list y_i + z_j ≥ p_i and the w-constraints, not z_j ≥ 0 → z ≥ 0 is a constraint of dmgi / dmgi5; reason: (4) is defined from dual feasibility of (3), which has z ≥ 0 (p. 17), and the proofs of Proposition 3 (p. 41) and Lemma 2 (p. 44) use it; without it a plant with no arcs makes (4) unbounded below
--   - encoding: capacities C_j (sign not stated) → hypothesis 0 ≤ C j; reason: with a negative capacity the LP (1) is infeasible and g is undefined; only excludes undefined cases
--   - encoding: plants a_1..a_m, products b_1..b_n, categories S_1..S_T (1-based), margins P_1 < ... < P_T → Fin m, Fin n, cat : Fin n → Fin T (0-based), P : Fin T → ℝ with StrictMono P, p_i = P (cat i); reason: Lean indexing; same instances
--   - encoding: parameter set K = {k_tr : t = 1..T, r = 0..t−1} and binary w_itr → K : (t : Fin T) → Fin (t+1) → ℕ (K t r is k_{t+1,r}); w as a level map w i ≤ cat i + 1; reason: Lean indexing; one level per product is exactly the w-constraints of (4)
--   - reading: Definition 2.2: E := {d − µ | d ∈ U} is part-wise independently symmetric, and Definition 2.1 is stated for sets ⊂ ℝ^n_+ → the sign condition is imposed on U only (IsPartwiseSymmAround); E satisfies clauses (1)–(2) of Definition 2.1 (IsPartwiseSymmCore) and may have negative entries; reason: E is the set of estimation errors around µ (p. 14), which fluctuate in both directions; applying ℝ^n_+ to E would force d ≥ µ on all of U. Every set admitted by the literal reading is admitted here, so the statement covers the source's
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), Appendix A, Proposition 3, display (7), p. 41

import Mathlib
import Definitions.Def_FlexMargin_lpValue
import Definitions.Def_FlexMargin_robustMeasure
import Definitions.Def_FlexMargin_IsPartwiseSymmAround
import Definitions.Def_FlexMargin_InQ
import Definitions.Def_FlexMargin_dmgi
import Definitions.Def_FlexMargin_residualTerm

namespace FlexMargin

/-- **Proposition 3: the worst-case profit through the DMGI (corrected: margins nonnegative).**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), Appendix A, Proposition 3, display (7), p. 41: "For any uncertainty set U that is part-wise
independently symmetric around µ, the worst-case profit Rg(A,U) is given by Rg(A,U) = min_{K∈Q,ϵ∈E}
{ δK_µ(A) + Σ_{t=1}^T ( Σ_{r=0}^{t−1} βtr ( Σ_{i=Htr−ktr+1}^{Htr} ϵst,i ) ) }, (7) where ϵst := dst − µst
denotes the vector of demand residuals for each product category St."

The general system of §2 (pp. 10–11): plants \`Fin m\` with capacities \`C ≥ 0\`, products \`Fin n\`,
margins \`P_1 < ⋯ < P_T\` (\`P : Fin T → ℝ\`, 0-based, \`StrictMono P\`) and categories \`cat : Fin n → Fin T\`
(product \`i\` has margin \`p_i = P (cat i)\`); a design \`A\` is any set of (plant, product) arcs.
For every centre `μ` and every `U` part-wise independently symmetric around `μ`
(`FlexMargin.IsPartwiseSymmAround`), the worst case of `g(A, d)` over `U` equals the infimum, over
`K ∈ Q` (`FlexMargin.InQ`) and `ε ∈ E = {d − μ | d ∈ U}`, of `δ^K_μ(A)` (`FlexMargin.dmgi`) plus the
residual term (`FlexMargin.residualTerm`).

**Formalization Note.** (a) Correction: the margins are assumed nonnegative (`∀ t, 0 ≤ P t`, i.e.
`0 ≤ P_1`). With a negative margin (7) is false: `T = 1`, `P_1 = −1`, `n = m = 1`, `A = {(a_1, b_1)}`,
`C_1 = 1`, `μ = (1)`, `U = {(1)}`: `R^g = 0`, but `K = (k_{10} = 1)` gives `δ = −1` and (7) gives `−1`.
(b) Both sides are infima in `EReal`; they equal the paper's minima whenever those exist, and no
continuity or compactness is assumed. (c) `ε_{s_t,i}` lists `ε` on `S_t` in increasing product index. -/
theorem proposition_3 {m n T : ℕ} (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (P : Fin T → ℝ)
    (hP : StrictMono P) (hP0 : ∀ t, 0 ≤ P t) (cat : Fin n → Fin T) (μ : Fin n → ℝ)
    (A : Finset (Fin m × Fin n)) (U : Set (Fin n → ℝ)) (hU : IsPartwiseSymmAround cat μ U) :
    robustMeasure (fun B d => lpValue C (fun i => P (cat i)) B d) A U =
      ⨅ (K : (t : Fin T) → Fin (t.val + 1) → ℕ) (_ : InQ cat K),
        ⨅ ε ∈ {e : Fin n → ℝ | ∃ d ∈ U, e = d - μ},
          ((dmgi C P cat μ A K + residualTerm P cat K ε : ℝ) : EReal) := by sorry

end FlexMargin
