-- Prove2me | Theorems.Thm_DeepMFC_FiniteHorizon_proposition_7
-- name    : DeepMFC.FiniteHorizon.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:49.534166+00:00
-- url     : https://prove2.me/theorems/878cd28d-3858-4f60-8d00-7f0b1e4308e8
-- title:
--   Proposition 7, p. 4072 — inf_𝔸 J ≥ J^N(v̂) − c₁√(N^{−2/max(d,4)}(1 + ln N 𝟏_{d=4})) for the optimal feedback v̂
-- statement:
--   Assume (A1)–(A4), (B1)–(B3), (C1)–(C3), let $\hat\alpha$ be the minimizer (2.6), $\mu_t$ the flow of marginals of the MKV FBSDE (2.7) and $V$ its decoupling field, and define the feedback
--   $$\hat v(t,x)=\hat\alpha(t,x,\mu_t,V(t,x)).\qquad(3.3)$$
--   Then there is a constant $c_1$, depending only on the data, such that for every $N\ge1$,
--   $$\inf_{\alpha\in\mathbb A}J(\alpha)\ \ge\ J^N(\hat v)-c_1\sqrt{N^{-2/\max(d,4)}\big(1+\ln(N)\mathbf 1_{\{d=4\}}\big)}.$$
--   Here $J$ is the cost of Problem 1 on any probability space carrying a $d$-dimensional Wiener process and an independent $X_0\sim\mu_0$, and $J^N(\hat v)$ is the cost (3.1) of the $N$-agent system (3.2) driven by $\hat v$.
--
--   This is the first step of Theorem 3: replacing the McKean–Vlasov optimum by $N$ agents using the optimal feedback costs at most the Fournier–Guillin rate of convergence of empirical measures.
--
--   **Formalization Note.** The infimum is stated pointwise: for every admissible $\alpha$ on every Problem-1 space and every solution $X$ of (2.2), $J(\alpha)\ge J^N(\hat v)-\epsilon_1(N)$, where $J^N(\hat v)$ is evaluated on any Problem-3 space and any solution of (3.2). The constant $c_1$ is chosen before $N$ and before both spaces.
-- source:
--   Carmona, Laurière, Convergence analysis of machine learning algorithms for the numerical solution of mean field control and games: II—the finite horizon case, Ann. Appl. Probab. 32(6) (2022), https://doi.org/10.1214/21-AAP1715, p. 4072, Proposition 7, (3.3)

import Mathlib
import Definitions.Def_DeepMFC_FiniteHorizon_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DeepMFC.FiniteHorizon

theorem proposition_7 {d k : ℕ} (M : Model d k) (D : Deriv d k) (hC : Coeff M D)
    (αhat : ℝ → E d → Measure (E d) → E d → Fin k → ℝ) (μflow : ℝ → Measure (E d))
    (V : ℝ → E d → E d) (hD : DecouplingField M D αhat μflow V) :
    ∃ c₁ : ℝ, ∀ N : ℕ, 1 ≤ N →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : ℝ≥0 → Ω → E d) (X0 : Ω → E d),
        Setting1 M P W X0 →
      ∀ α : ℝ≥0 → Ω → Fin k → ℝ, Admissible M P W X0 α →
      ∀ X : ℝ≥0 → Ω → E d, Solves22 M P W X0 α X →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (W' : Fin N → ℝ≥0 → Ω' → E d)
        (X0' : Fin N → Ω' → E d), Setting3 M P' W' X0' →
      ∀ XN : Fin N → ℝ≥0 → Ω' → E d, Solves32 M P' W' X0' (vhat αhat μflow V) XN →
        JN M P' (vhat αhat μflow V) XN
          - c₁ * Real.sqrt ((N : ℝ) ^ (-(2 : ℝ) / ((max d 4 : ℕ) : ℝ))
              * (1 + Real.log N * (if d = 4 then 1 else 0)))
          ≤ J M P α X := by sorry

end DeepMFC.FiniteHorizon
