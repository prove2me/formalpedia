-- Prove2me | Theorems.Thm_CasinoCPT_Embedding_proposition_A_1_iii
-- name    : CasinoCPT.Embedding.proposition_A_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:34.127294+00:00
-- url     : https://prove2.me/theorems/cc0359c5-9860-493b-9880-989983fb1256
-- title:
--   Proposition A.1 (iii), p. 44, (17) — one step of the stopped walk changes U only on K = t − 1 + 2ℤ
-- statement:
--   Let $S$ be a standard symmetric random walk on a casino space with filtration $(\mathcal F_t)$, and let $\tau$ be an $(\mathcal F_t)$-stopping time such that $\{S_{\tau\wedge t}:t\in\mathbb N\}$ is uniformly integrable. Fix $t\ge1$ and let $\mathcal K=\{t-1+2j:j\in\mathbb Z\}$. Then for every $x\in\mathbb Z$,
--   $$U_{S_{\tau\wedge t}}(x)=U_{S_{\tau\wedge(t-1)}}(x)+P(S_{t-1}=x,\ \tau\ge t)\,\mathbf 1_{x\in\mathcal K}.\tag{17}$$
--   In particular, if $t$ is odd then $U_{S_{\tau\wedge t}}(x)=U_{S_{\tau\wedge(t-1)}}(x)$ for every odd $x$, and if $t$ is even the same holds for every even $x$.
--
--   Identity (17) is the one-step recursion that the proof of Proposition A.3 compares with the recursion (6) defining $U^\mu_t$.
--
--   **Formalization Note.** Membership $x\in\mathcal K$ is written as "$x-(t-1)$ is even".
-- source:
--   Hu, Obłój & Zhou, When to Quit Gambling, if You Must!, arXiv:2102.03157v1, p. 44, Proposition A.1 (iii), (17)

import Mathlib
import Definitions.Def_CasinoCPT_Embedding_Model

namespace CasinoCPT.Embedding

open MeasureTheory ProbabilityTheory

/-- Proposition A.1 (iii), p. 44, eq. (17): let `τ` be an `(F t)`-stopping time such that
`{S_{τ∧t} : t ∈ ℕ}` is uniformly integrable, fix `t ≥ 1` and let
`K = {t - 1 + 2j : j ∈ ℤ}`. Then for every integer `x`,
`U_{S_{τ∧t}}(x) = U_{S_{τ∧(t-1)}}(x) + P(S_{t-1} = x, τ ≥ t) 1_{x ∈ K}`. In particular, if `t` is
odd the two potentials agree at every odd `x`, and if `t` is even they agree at every even
`x`. Membership `x ∈ K` is `Even (x - (t - 1))`. -/
theorem proposition_A_1_iii {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℕ mΩ) (S : ℕ → Ω → ℤ) (ξ : Ω → ℝ) (hS : IsCasinoSpace P F S ξ)
    (τ : Ω → ℕ∞) (hτ : IsStoppingTime F τ)
    (hUI : UniformIntegrable
      (fun (t : ℕ) (ω : Ω) => ((stoppedValue S (fun ω => min (τ ω) (t : ℕ∞)) ω : ℤ) : ℝ)) 1 P)
    (t : ℕ) (ht : 1 ≤ t) :
    (∀ x : ℤ,
      potential (P.map (stoppedValue S (fun ω => min (τ ω) (t : ℕ∞)))) (x : ℝ) =
        potential (P.map (stoppedValue S (fun ω => min (τ ω) ((t - 1 : ℕ) : ℕ∞)))) (x : ℝ) +
          (if Even (x - ((t : ℤ) - 1)) then
            (P {ω | S (t - 1) ω = x ∧ (t : ℕ∞) ≤ τ ω}).toReal else 0)) ∧
      (Odd t → ∀ x : ℤ, Odd x →
        potential (P.map (stoppedValue S (fun ω => min (τ ω) (t : ℕ∞)))) (x : ℝ) =
          potential (P.map (stoppedValue S (fun ω => min (τ ω) ((t - 1 : ℕ) : ℕ∞)))) (x : ℝ)) ∧
      (Even t → ∀ x : ℤ, Even x →
        potential (P.map (stoppedValue S (fun ω => min (τ ω) (t : ℕ∞)))) (x : ℝ) =
          potential (P.map (stoppedValue S (fun ω => min (τ ω) ((t - 1 : ℕ) : ℕ∞)))) (x : ℝ)) := by sorry

end CasinoCPT.Embedding
