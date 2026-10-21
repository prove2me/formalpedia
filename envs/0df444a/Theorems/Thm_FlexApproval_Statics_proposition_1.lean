-- Prove2me | Theorems.Thm_FlexApproval_Statics_proposition_1
-- name    : FlexApproval.Statics.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:59.227104+00:00
-- url     : https://prove2.me/theorems/a982f3b2-7c0c-4f04-b85c-a67b4d16bcbf
-- title:
--   Proposition 1, p. 13 — α* increases in Q_E, C_AE, C_RE, µ_I, µ_AB, decreases in Q_I, C_AI, λ, µ_CT, and (if ψ_E(α*) < 1) increases in p, decreases in µ_E
-- statement:
--   Consider the drug-approval model with expected net benefit $V(\alpha)$ and optimal approval policies $\alpha^*\in\arg\max_{\alpha\in[0,1]}V(\alpha)$. The optimal approval policy $\alpha^*$ is
--
--   1. (a) nondecreasing in each of $Q_E$, $C_{AE}$, $C_{RE}$, $\mu_I$ and $\mu_{AB}$;
--   2. (b) nonincreasing in each of $Q_I$, $C_{AI}$, $\lambda$ and $\mu_{CT}$;
--   3. (c) nondecreasing in $p$ and nonincreasing in $\mu_E$, under the additional assumption that $\psi_E(\alpha^*)<1$.
--
--   Precisely, for each listed parameter $x$: take two parameter vectors that agree except in $x$, with values $x_1\le x_2$, both satisfying the standing assumptions, and let $\alpha_1^*$ and $\alpha_2^*$ be optimal policies for them. Then
--   $$\alpha_1^*\le\alpha_2^*\ \text{(increasing)}\qquad\text{or}\qquad \alpha_2^*\le\alpha_1^*\ \text{(decreasing)}.$$
--   In (c) the assumption is that $\psi_E(\alpha^*)<1$ holds at every optimal policy $\alpha^*$ of every parameter vector obtained by giving $x$ a value in $[x_1,x_2]$.
--
--   In words: approval should be more stringent for diseases with many compounds in development or short trials, and less stringent for diseases with high trial attrition, large health benefits or high costs of rejecting an effective drug.
--
--   **Formalization Note** "Increasing" and "decreasing" are weak, as the proof gives derivative signs $\ge0$ and $\le0$. The comparison is for arbitrary maximizers (Theorem 1 shows there is exactly one). Parameters other than $x$ are fixed by a record update of one parameter vector. The paper states the side condition of (c) at $\alpha^*$; since its proof integrates the sign of $\partial\alpha^*/\partial x$ along the parameter, the condition is required along the whole segment $[x_1,x_2]$, not only at its endpoints. The standing assumptions (listed with the model) are added; the paper does not state them.
-- source:
--   Bravo, Corcoran & Long, Flexible Drug Approval Policies, SSRN working paper 3027263 (version of 17 Jul 2019), p. 13, Proposition 1 (a)–(c)

import Mathlib
import Definitions.Def_FlexApproval_Statics_Model

namespace FlexApproval.Statics

/-- Proposition 1, p. 13. The optimal approval policy `α*` is
(a) increasing in `Q_E`, `C_AE`, `C_RE`, `µ_I` and `µ_AB`,
(b) decreasing in `Q_I`, `C_AI`, `λ` and `µ_CT`,
(c) increasing in `p` and decreasing in `µ_E` under the additional assumption that `ψ_E(α*) < 1`.

Each clause compares two parameter vectors that differ only in the named field (record update of
the same `P`), both satisfying the standing assumptions, with `x₁ ≤ x₂`, and any optimal policies
`a₁`, `a₂` of the two; monotonicity is weak. In (c) the assumption `ψ_E(α*) < 1` is required at the
optimal policy for every value of the parameter between `x₁` and `x₂`. -/
theorem proposition_1 :
    -- (a) increasing in Q_E
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with QE := x₁ } : Params).Standing → ({ P with QE := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with QE := x₁ } a₁ → IsOptimal { P with QE := x₂ } a₂ → a₁ ≤ a₂) ∧
    -- (a) increasing in C_AE
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with CAE := x₁ } : Params).Standing → ({ P with CAE := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with CAE := x₁ } a₁ → IsOptimal { P with CAE := x₂ } a₂ → a₁ ≤ a₂) ∧
    -- (a) increasing in C_RE
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with CRE := x₁ } : Params).Standing → ({ P with CRE := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with CRE := x₁ } a₁ → IsOptimal { P with CRE := x₂ } a₂ → a₁ ≤ a₂) ∧
    -- (a) increasing in µ_I
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with muI := x₁ } : Params).Standing → ({ P with muI := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with muI := x₁ } a₁ → IsOptimal { P with muI := x₂ } a₂ → a₁ ≤ a₂) ∧
    -- (a) increasing in µ_AB
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with muAB := x₁ } : Params).Standing → ({ P with muAB := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with muAB := x₁ } a₁ → IsOptimal { P with muAB := x₂ } a₂ → a₁ ≤ a₂) ∧
    -- (b) decreasing in Q_I
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with QI := x₁ } : Params).Standing → ({ P with QI := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with QI := x₁ } a₁ → IsOptimal { P with QI := x₂ } a₂ → a₂ ≤ a₁) ∧
    -- (b) decreasing in C_AI
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with CAI := x₁ } : Params).Standing → ({ P with CAI := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with CAI := x₁ } a₁ → IsOptimal { P with CAI := x₂ } a₂ → a₂ ≤ a₁) ∧
    -- (b) decreasing in λ
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with lam := x₁ } : Params).Standing → ({ P with lam := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with lam := x₁ } a₁ → IsOptimal { P with lam := x₂ } a₂ → a₂ ≤ a₁) ∧
    -- (b) decreasing in µ_CT
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with muCT := x₁ } : Params).Standing → ({ P with muCT := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with muCT := x₁ } a₁ → IsOptimal { P with muCT := x₂ } a₂ → a₂ ≤ a₁) ∧
    -- (c) increasing in p, if ψ_E(α*) < 1 along the way
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with p := x₁ } : Params).Standing → ({ P with p := x₂ } : Params).Standing →
      x₁ ≤ x₂ →
      (∀ x ∈ Set.Icc x₁ x₂, ∀ a : ℝ, IsOptimal { P with p := x } a →
        psiE { P with p := x } a < 1) →
      IsOptimal { P with p := x₁ } a₁ → IsOptimal { P with p := x₂ } a₂ → a₁ ≤ a₂) ∧
    -- (c) decreasing in µ_E, if ψ_E(α*) < 1 along the way
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with muE := x₁ } : Params).Standing → ({ P with muE := x₂ } : Params).Standing →
      x₁ ≤ x₂ →
      (∀ x ∈ Set.Icc x₁ x₂, ∀ a : ℝ, IsOptimal { P with muE := x } a →
        psiE { P with muE := x } a < 1) →
      IsOptimal { P with muE := x₁ } a₁ → IsOptimal { P with muE := x₂ } a₂ → a₂ ≤ a₁) := by sorry

end FlexApproval.Statics
