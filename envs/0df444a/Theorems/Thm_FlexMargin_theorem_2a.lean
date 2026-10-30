-- Prove2me | Theorems.Thm_FlexMargin_theorem_2a
-- name    : FlexMargin.theorem_2a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:44:41.169602+00:00
-- url     : https://prove2.me/theorems/c3bdb304-cf5f-4f1f-a43c-18d2305849e1
-- title:
--   Theorem 2(a): DMGI dominance implies robust dominance
-- statement:
--   Consider a system with $m$ plants of capacities $C\ge0$ and $n$ products in categories with margins $P_1<\dots<P_T$. Fix $h$ strictly increasing in its first argument, so that $R=R^f$ with $f(\mathcal A,d)=h\big(g(\mathcal A,d),\sum d_{s_1},\dots,\sum d_{s_T}\big)$ belongs to $\Gamma$, and fix $\mu$. If two designs satisfy
--
--   $$
--   \delta^K_\mu(\mathcal A_1)\ge\delta^K_\mu(\mathcal A_2)\qquad\text{for all }K\in Q,
--   $$
--
--   then $R(\mathcal A_1,U)\ge R(\mathcal A_2,U)$ for every uncertainty set $U$ that is part-wise independently symmetric around $\mu$.
--
--   This sufficient condition reduces the comparison of designs under every measure in $\Gamma$ to finitely many integer programs.
--
--   Differences from the source:
--   - reading: δ^K(A_1,U) ≥ δ^K(A_2,U) for all K ∈ Q, then R(A_1,U) ≥ R(A_2,U) for any U → δ^K_μ(A_1) ≥ δ^K_μ(A_2) for all K ∈ Q (μ fixed), then R(A_1,U) ≥ R(A_2,U) for every U symmetric around μ; reason: δ depends on U only through its centre μ; the proof (p. 43) applies Theorem 1 with that μ
--   - generalization: R^f(A,U) = min_{d∈U} f(A,d), with f continuous in d so that the minimum exists → R is the infimum in EReal over U (robustMeasure); no continuity of f, no compactness of U; reason: the EReal infimum equals the minimum whenever it exists, so the statement specializes to the source's
--   - reading: (4)/(5) list y_i + z_j ≥ p_i and the w-constraints, not z_j ≥ 0 → z ≥ 0 is a constraint of dmgi / dmgi5; reason: (4) is defined from dual feasibility of (3), which has z ≥ 0 (p. 17), and the proofs of Proposition 3 (p. 41) and Lemma 2 (p. 44) use it; without it a plant with no arcs makes (4) unbounded below
--   - encoding: capacities C_j (sign not stated) → hypothesis 0 ≤ C j; reason: with a negative capacity the LP (1) is infeasible and g is undefined; only excludes undefined cases
--   - encoding: plants a_1..a_m, products b_1..b_n, categories S_1..S_T (1-based), margins P_1 < ... < P_T → Fin m, Fin n, cat : Fin n → Fin T (0-based), P : Fin T → ℝ with StrictMono P, p_i = P (cat i); reason: Lean indexing; same instances
--   - encoding: parameter set K = {k_tr : t = 1..T, r = 0..t−1} and binary w_itr → K : (t : Fin T) → Fin (t+1) → ℕ (K t r is k_{t+1,r}); w as a level map w i ≤ cat i + 1; reason: Lean indexing; one level per product is exactly the w-constraints of (4)
--   - reading: Definition 2.2: E := {d − µ | d ∈ U} is part-wise independently symmetric, and Definition 2.1 is stated for sets ⊂ ℝ^n_+ → the sign condition is imposed on U only (IsPartwiseSymmAround); E satisfies clauses (1)–(2) of Definition 2.1 (IsPartwiseSymmCore) and may have negative entries; reason: E is the set of estimation errors around µ (p. 14), which fluctuate in both directions; applying ℝ^n_+ to E would force d ≥ µ on all of U. Every set admitted by the literal reading is admitted here, so the statement covers the source's
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §3.2, Theorem 2(a), p. 18

import Mathlib
import Definitions.Def_FlexMargin_marginMeasure
import Definitions.Def_FlexMargin_IsMonotonicInProfit
import Definitions.Def_FlexMargin_robustMeasure
import Definitions.Def_FlexMargin_IsPartwiseSymmAround
import Definitions.Def_FlexMargin_InQ
import Definitions.Def_FlexMargin_dmgi

namespace FlexMargin

/-- **Theorem 2(a): the DMGI comparison is a sufficient condition for robust dominance.**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §3.2, Theorem 2(a), p. 18: "Fix a robust measure R ∈ Γ. Then the following statements hold:
(a) If δK(A1,U) ≥ δK(A2,U) for all K ∈ Q, then R(A1,U) ≥ R(A2,U) for any part-wise independently
symmetric perturbation uncertainty set U."

The general system of §2 (pp. 10–11): plants \`Fin m\` with capacities \`C ≥ 0\`, products \`Fin n\`,
margins \`P_1 < ⋯ < P_T\` (\`P : Fin T → ℝ\`, 0-based, \`StrictMono P\`) and categories \`cat : Fin n → Fin T\`
(product \`i\` has margin \`p_i = P (cat i)\`); a design \`A\` is any set of (plant, product) arcs.
Fix `h` strictly increasing in its first argument (so `R = R^f` with `f = FlexMargin.marginMeasure C P
cat h` is in Γ) and a centre `μ`. If `δ^K_μ(A_2) ≤ δ^K_μ(A_1)` (`FlexMargin.dmgi`) for every `K ∈ Q`, then
`R(A_2, U) ≤ R(A_1, U)` for every `U` part-wise independently symmetric around `μ`.

**Formalization Note.** (a) Reading: the page's "δK(A1,U)" is `δ^K_μ(A_1)` with `μ` the centre of
`U` (the proof, p. 43, applies Theorem 1 with that `μ`), so `μ` is fixed and `U` ranges over the sets
symmetric around it. (b) `R` is the `EReal` infimum (`FlexMargin.robustMeasure`); no continuity of `f`.
(c) No sign condition on the margins (the paper states none). -/
theorem theorem_2a {m n T : ℕ} (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (P : Fin T → ℝ)
    (hP : StrictMono P) (cat : Fin n → Fin T) (h : ℝ → (Fin T → ℝ) → ℝ)
    (hh : IsMonotonicInProfit h) (μ : Fin n → ℝ) (A1 A2 : Finset (Fin m × Fin n))
    (hδ : ∀ K : (t : Fin T) → Fin (t.val + 1) → ℕ, InQ cat K →
      dmgi C P cat μ A2 K ≤ dmgi C P cat μ A1 K)
    (U : Set (Fin n → ℝ)) (hU : IsPartwiseSymmAround cat μ U) :
    robustMeasure (marginMeasure C P cat h) A2 U ≤ robustMeasure (marginMeasure C P cat h) A1 U := by sorry

end FlexMargin
