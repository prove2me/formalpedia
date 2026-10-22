-- Prove2me | Theorems.Thm_DynamicAssortment_Separation_display9_eta_local_bound
-- name    : DynamicAssortment.Separation.display9_eta_local_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T10:49:38.228885+00:00
-- url     : https://prove2.me/theorems/0669c5fe-f752-47f1-a4df-3b4dae98897f
-- title:
--   Display (9) (p. 402) — ‖μ − μ̂_t‖_{A_j} ≤ κ(ϵ)‖p − p̂_t‖_{A_j} whenever ‖p − p̂_t‖_{A_j} < ϵ
-- statement:
--   In the setting of Theorem 2, write $p_i=p_i(A_j,\mu)$ for $i\in A_j$. There is $\epsilon_0>0$ such that, for every $\epsilon\in(0,\epsilon_0]$, there is a constant $1<\kappa(\epsilon)<\infty$ with the following property. For every test assortment $A_j$, every sequence of past assortments $S_u$ and purchases $h_u$, and every $t$,
--   $$\|p-\hat p_t(A_j)\|_{A_j}<\epsilon\ \Longrightarrow\ \|\mu-\hat\mu_t\|_{A_j}\le\kappa(\epsilon)\,\|p-\hat p_t(A_j)\|_{A_j},$$
--   where $\hat p_t(A_j)$ is the frequency estimator (4) and $\hat\mu_t$ the mean-utility estimate $\hat\mu_{t,i}=\eta(\hat p_t(A_j))_i$.
--
--   It converts closeness of the empirical purchase frequencies into closeness of the estimated mean utilities, and is the deterministic link between Lemma 1 and display (10).
--
--   **Formalization Note** The page asserts (9) "for any $\epsilon>0$". Since $\eta$ is only locally Lipschitz and a far-off frequency vector can leave $\eta$'s domain, the statement is made for $\epsilon$ up to some $\epsilon_0>0$, which is all the proof of Theorem 2 uses. The page's "$A_j\subseteq\mathcal A$" is read as $A_j\in\mathcal A$, and $\|\cdot\|_A$ carries absolute values.
-- source:
--   Sauré, Zeevi, Optimal Dynamic Assortment Planning with Demand Learning, Manuf. Serv. Oper. Manag. 15(3), 2013, p. 402, App. A, proof of Theorem 2, Step 1, display (9)

import Mathlib
import Definitions.Def_DynamicAssortment_Separation_ChoiceModel
import Definitions.Def_DynamicAssortment_Separation_History
import Definitions.Def_DynamicAssortment_Separation_SeparationPolicy
import Definitions.Def_DynamicAssortment_Separation_AssumptionOne

namespace DynamicAssortment.Separation

/-- Display (9) (App. A, p. 402): for every small enough `ε > 0` there is `1 < κ(ε) < ∞` with
`‖μ - μ̂_t‖_{A_j} ≤ κ(ε) ‖p - p̂_t‖_{A_j}` whenever `‖p - p̂_t‖_{A_j} < ε`, where
`p_i = p_i(A_j, μ)`; deterministic, for any past assortments `S`, purchases `h` and time `t`. -/
theorem display9_eta_local_bound {N C : ℕ} (hC : 1 ≤ C) (hCN : C ≤ N)
    (f : ℝ → ℝ) (hf : IsNoiseDensity f) (w : Fin N → ℝ) (hw : ∀ i, 0 < w i)
    (μ : Fin N → ℝ) (opt : (Fin N → ℝ) → Finset (Fin N))
    (hopt : IsOptimalSelection f w C opt) (huniq : UniqueOptimum f w C μ (opt μ))
    (eta : Finset (Fin N) → (Fin N → ℝ) → (Fin N → ℝ)) (hid : Identifiability f C eta) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ κ : ℝ, 1 < κ ∧
      ∀ j < numTests N C, ∀ (S : ℕ → Finset (Fin N)) (h : ℕ → Option (Fin N)) (t : ℕ),
        normOn (testAssortment N C j) ((fun i => choiceProb f μ (testAssortment N C j) i) -
            freqEstimate S h (testAssortment N C j) t) < ε →
          normOn (testAssortment N C j) (μ - muHat C eta S h t) ≤
            κ * normOn (testAssortment N C j) ((fun i => choiceProb f μ (testAssortment N C j) i) -
              freqEstimate S h (testAssortment N C j) t) := by sorry

end DynamicAssortment.Separation
