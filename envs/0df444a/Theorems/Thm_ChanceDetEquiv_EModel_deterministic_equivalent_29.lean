-- Prove2me | Theorems.Thm_ChanceDetEquiv_EModel_deterministic_equivalent_29
-- name    : ChanceDetEquiv.EModel.deterministic_equivalent_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:12:10.101277+00:00
-- url     : https://prove2.me/theorems/f1d503d9-1608-41a5-ae8a-63294ea79d6c
-- title:
--   'E Model', pp. 25–29 — under normality, (18) is equivalent to the convex program (29)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $A$ a constant $m\times n$ matrix with rows $a_i'$, and $b:\Omega\to\mathbb R^m$, $c:\Omega\to\mathbb R^n$ random vectors. Assume:
--
--   1. every $b_k$ is square integrable, every $c_j$ and every product $c_jb_k$ is integrable;
--   2. $b$ and $c$ are uncorrelated: $E(c_jb_k)=E(c_j)E(b_k)$ for all $j,k$;
--   3. for every $n\times m$ decision rule $D$ and every row $i$, the variate $a_i'Db-b_i$ is normally distributed (zero variance allowed);
--   4. $\tfrac12<\alpha_i<1$ for every $i$, and $K_{\alpha_i}=\Phi^{-1}(\alpha_i)$.
--
--   Consider the E-model (18), $\max E(c'x)$ subject to $P(a_i'x\le b_i)\ge\alpha_i$ $(i=1,\dots,m)$ and $x=Db$, and the program (29),
--   $$\min\ -\mu_c'D\mu_b\quad\text{s.t.}\quad \mu_i(D)-v_i\ge0,\quad -K_{\alpha_i}^2\sigma_i^2(D)+K_{\alpha_i}^2\mu_i^2(D)+v_i^2\ge0,\quad v_i\ge0,$$
--   with $\sigma_i^2(D)=E(a_i'Db-b_i)^2$ and $\mu_i(D)=\mu_{b_i}-a_i'D\mu_b$ as in (30). Then:
--
--   1. for every $D$: $D$ satisfies the chance constraints of (18) if and only if there is $v\in\mathbb R^m$ with $(D,v)$ satisfying (29);
--   2. for every $D$: $E(c'Db)=\mu_c'D\mu_b$;
--   3. the set of pairs $(D,v)$ satisfying (29) is convex.
--
--   In particular (18) and (29) have the same feasible decision rules. Their objectives are negatives of each other, so their optimal decision rules coincide and their optimal values have opposite signs: (29) is a deterministic equivalent of (18), and it is a convex program.
--
--   **Formalization Note** The paper's "deterministic equivalent … convex programming problem" is made explicit as the three conjuncts above. The chance constraints are row-wise, as in (3). Normality is assumed per row and per decision rule, as on p. 27, not as joint normality of $b$. $\alpha_i<1$ is added so that $K_{\alpha_i}$ is finite; the positive-variance assumption of (22) is not made, as footnote † of p. 28 asks. $\sigma_i^2(D)$ is the raw second moment printed in (30).
-- source:
--   Charnes and Cooper, Deterministic Equivalents for Optimizing and Satisficing under Chance Constraints, Oper. Res. 11 (1963), pp. 25–29, 'E Model', Eqs. (18), (19a), (29), (30) and the paragraphs after (30)

import Mathlib
import Definitions.Def_ChanceDetEquiv_EModel_Model

open MeasureTheory ProbabilityTheory Matrix

namespace ChanceDetEquiv.EModel

/-- **'E Model', (18) ⇔ (29)–(30)**, pp. 25–29. Let `A` be a constant `m × n` matrix, `b`, `c`
random vectors with square-integrable `b_k`, integrable `c_j` and `c_j b_k`, `b` and `c`
uncorrelated, every variate `a_i'Db − b_i` normal (zero variance allowed), and `½ < α_i < 1`.
Then (i) a decision rule `D` satisfies the chance constraints of (18) iff some `v` makes
`(D, v)` satisfy (29); (ii) `E(c'Db) = μ_c'Dμ_b` for every `D`; (iii) the feasible set of (29)
is convex in `(D, v)`. -/
theorem deterministic_equivalent_29 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Ω → Fin m → ℝ) (c : Ω → Fin n → ℝ) (α : Fin m → ℝ)
    (hb : ∀ k, MemLp (fun ω => b ω k) 2 P)
    (hc : ∀ j, Integrable (fun ω => c ω j) P)
    (hcb : ∀ j k, Integrable (fun ω => c ω j * b ω k) P)
    (huncorr : ∀ j k, ∫ ω, c ω j * b ω k ∂P = (∫ ω, c ω j ∂P) * (∫ ω, b ω k ∂P))
    (hnormal : RowsNormal P A b)
    (hα_lo : ∀ i, 1 / 2 < α i) (hα_hi : ∀ i, α i < 1) :
    (∀ D : Matrix (Fin n) (Fin m) ℝ, IsChanceFeasible18 P A b α D ↔ ∃ v, Sys29 P A b α D v) ∧
    (∀ D : Matrix (Fin n) (Fin m) ℝ, expectedObjective P b c D = detObjective P b c D) ∧
    Convex ℝ {p : Matrix (Fin n) (Fin m) ℝ × (Fin m → ℝ) | Sys29 P A b α p.1 p.2} := by sorry

end ChanceDetEquiv.EModel
