-- Prove2me | Theorems.Thm_DynSetValue_DPP_lemma_3_10_ii
-- name    : DynSetValue.DPP.lemma_3_10_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:21.192313+00:00
-- url     : https://prove2.me/theorems/65a2ff79-5497-461b-be19-8252ffeec620
-- title:
--   Lemma 3.10(ii) — approximation of admissible controls
-- statement:
--   For any admissible profile $\alpha$ and $\delta>0$, there is an admissible profile $\alpha^\delta$ constant on the intervals of a finite partition $0=t_0<\cdots<t_n=T$. Each value $\alpha^\delta_{t_i}$ is an $\mathcal F_{t_i}$-measurable, uniformly continuous function of the path, and
--
--   $$
--   \mathbb E^{\mathbb P_0}\!\left[
--   \int_0^T\min\bigl(\|\alpha^\delta_t-\alpha_t\|,1\bigr)\,dt
--   \right]\le\delta.
--   $$
--
--   This keeps the full progressive-control class available while allowing finite-step approximations.
--
--   **Formalization Note** The value at $T$ is the last partition value. Nonnegative extended integrals prevent default-zero values for an inadmissible integrand.
-- source:
--   Feinstein, Rudloff, Zhang, Dynamic set values for nonzero sum games with multiple equilibriums, arXiv:2002.00449v2, p. 28, Lemma 3.10(ii)

import Mathlib
import Definitions.Def_DynSetValue_DPP_Game

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace DynSetValue.DPP

/-- Lemma 3.10(ii), p. 28. -/
theorem lemma_3_10_ii {T : ℝ} (hT : 0 < T) {d N : ℕ}
    (G : Game T hT d N) (P0 : Measure (Ω T d))
    (hP0 : IsWiener hT P0)
    (α : Profile hT G) (hα : IsProfile hT G P0 α)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (n : ℕ) (hn : 0 < n)
      (times : Fin (n + 1) → Interval T)
      (c : Fin n → Ω T d → ActionDomain G.actions)
      (αδ : Profile hT G),
      StrictMono times ∧
      times 0 = ⟨0, ⟨le_refl _, hT.le⟩⟩ ∧
      times (Fin.last n) = ⟨T, ⟨hT.le, le_refl _⟩⟩ ∧
      (∀ i, Measurable[𝓕 hT P0 (times (Fin.castSucc i)).1] (c i) ∧
        UniformContinuous (c i)) ∧
      (∀ i (s : Interval T) (ω : Ω T d),
        (times (Fin.castSucc i)).1 ≤ s.1 →
        s.1 < (times i.succ).1 →
        ∀ j : Fin N, αδ j s ω = (c i ω).1 j) ∧
      (∀ ω j, αδ j (clamp T hT T) ω = (c ⟨n - 1, by omega⟩ ω).1 j) ∧
      IsProfile hT G P0 αδ ∧
      (∫⁻ ω : Ω T d,
        ∫⁻ s in Set.Ioc (0 : ℝ) T,
          ENNReal.ofReal
            (min (actionDist G.actions
              (fun j => αδ j (clamp T hT s) ω)
              (fun j => α j (clamp T hT s) ω)) 1) ∂volume ∂P0) ≤
        ENNReal.ofReal δ := by sorry

end DynSetValue.DPP
