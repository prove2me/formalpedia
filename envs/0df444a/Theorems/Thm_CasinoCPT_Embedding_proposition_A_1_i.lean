-- Prove2me | Theorems.Thm_CasinoCPT_Embedding_proposition_A_1_i
-- name    : CasinoCPT.Embedding.proposition_A_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:47.876966+00:00
-- url     : https://prove2.me/theorems/9762a78a-5a87-4c6c-948b-1f709de403a9
-- title:
--   Proposition A.1 (i), p. 44 — U_{S_{τ∧t}} is convex, |x| ≤ U_{S_{τ∧t}} ≤ U_{S_τ}, and = |x| off (−t, t)
-- statement:
--   Let $S$ be a standard symmetric random walk on a casino space with filtration $(\mathcal F_t)$, and let $\tau$ be an $(\mathcal F_t)$-stopping time such that the family $\{S_{\tau\wedge t}:t\in\mathbb N\}$ is uniformly integrable. Then for every $t\in\mathbb N$:
--
--   1. the potential $U_{S_{\tau\wedge t}}$ is a convex function on $\mathbb R$;
--   2. for every $x\in\mathbb R$,
--   $$U_{S_\tau}(x)\ \ge\ U_{S_{\tau\wedge t}}(x)\ \ge\ |x|;$$
--   3. $U_{S_{\tau\wedge t}}(x)=|x|$ for every $x\notin(-t,t)$.
--
--   These are the standard properties of potentials of a stopped martingale, recalled at the start of the proof of Theorem 3.1.
--
--   **Formalization Note.** $U_{S_\sigma}$ is the potential of the push-forward of $P$ under `stoppedValue S σ`. On the event $\{\tau=\infty\}$ Mathlib's `stoppedValue` reads $S_0$. That event is null under the hypotheses, because a uniformly integrable stopped walk converges almost surely and a walk with steps $\pm1$ cannot converge. So the law of $S_\tau$ is the paper's.
-- source:
--   Hu, Obłój & Zhou, When to Quit Gambling, if You Must!, arXiv:2102.03157v1, p. 44, Proposition A.1 (i)

import Mathlib
import Definitions.Def_CasinoCPT_Embedding_Model

namespace CasinoCPT.Embedding

open MeasureTheory ProbabilityTheory

/-- Proposition A.1 (i), p. 44: let `τ` be an `(F t)`-stopping time such that
`{S_{τ∧t} : t ∈ ℕ}` is uniformly integrable. Then for every `t ∈ ℕ`, `U_{S_{τ∧t}}` is convex,
`U_{S_τ}(x) ≥ U_{S_{τ∧t}}(x) ≥ |x|` for all real `x`, and `U_{S_{τ∧t}}(x) = |x|` for
`x ∉ (-t, t)`. Here `U_{S_σ}` is the potential of the law `P.map (stoppedValue S σ)`. -/
theorem proposition_A_1_i {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℕ mΩ) (S : ℕ → Ω → ℤ) (ξ : Ω → ℝ) (hS : IsCasinoSpace P F S ξ)
    (τ : Ω → ℕ∞) (hτ : IsStoppingTime F τ)
    (hUI : UniformIntegrable
      (fun (t : ℕ) (ω : Ω) => ((stoppedValue S (fun ω => min (τ ω) (t : ℕ∞)) ω : ℤ) : ℝ)) 1 P)
    (t : ℕ) :
    ConvexOn ℝ Set.univ (potential (P.map (stoppedValue S (fun ω => min (τ ω) (t : ℕ∞))))) ∧
      (∀ x : ℝ,
        potential (P.map (stoppedValue S (fun ω => min (τ ω) (t : ℕ∞)))) x ≤
            potential (P.map (stoppedValue S τ)) x ∧
          |x| ≤ potential (P.map (stoppedValue S (fun ω => min (τ ω) (t : ℕ∞)))) x) ∧
      (∀ x : ℝ, x ∉ Set.Ioo (-(t : ℝ)) (t : ℝ) →
        potential (P.map (stoppedValue S (fun ω => min (τ ω) (t : ℕ∞)))) x = |x|) := by sorry

end CasinoCPT.Embedding
