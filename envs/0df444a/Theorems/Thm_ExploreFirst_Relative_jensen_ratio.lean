-- Prove2me | Theorems.Thm_ExploreFirst_Relative_jensen_ratio
-- name    : ExploreFirst.Relative.jensen_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:12:49.738823+00:00
-- url     : https://prove2.me/theorems/e742040e-789f-4654-ac6a-1c8afbee36bd
-- title:
--   Proof of Theorem 3, p. 12 — Jensen for x ↦ x/(1 + x): 𝔼[N⁺_a/(N⁺_a + N⁺_{a⋆})] ≤ r/(1 + r)
-- statement:
--   Let $\psi$ be any strategy, $\underline{\nu}$ any bandit problem, $a$ and $a^\star$ any two arms and $T \ge 0$. With $N^+_{\psi,k}(T) = \max\{N_{\psi,k}(T), 1\}$,
--   $$\mathbb{E}_{\underline{\nu}}\left[\frac{N^+_{\psi,a}(T)}{N^+_{\psi,a}(T) + N^+_{\psi,a^\star}(T)}\right] = \mathbb{E}_{\underline{\nu}}\left[\frac{N^+_{\psi,a}(T)/N^+_{\psi,a^\star}(T)}{1 + N^+_{\psi,a}(T)/N^+_{\psi,a^\star}(T)}\right] \le \frac{r}{1 + r}, \qquad r = \mathbb{E}_{\underline{\nu}}\left[\frac{N^+_{\psi,a}(T)}{N^+_{\psi,a^\star}(T)}\right].$$
--
--   The inequality is Jensen's inequality for the concave function $x \mapsto x/(1+x)$ on $[0,\infty)$. It converts the lower bound (12) on the expectation of the share $N^+_a/(N^+_a + N^+_{a^\star})$ into a bound on the expected ratio $r$ that Theorem 3 controls.
--
--   **Formalization Note** The statement holds for every kernel policy and every bandit problem; no symmetry or model hypothesis is needed. The two equal-and-less-than relations of the display are stated as a conjunction.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 12, proof of Theorem 3, display following (12)

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_ExploreFirst_Relative_Setting

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace ExploreFirst.Relative

theorem jensen_ratio {K : ℕ} (π : BanditPolicy K) (ν : StochasticBandit K) (a a' : Fin K)
    (T : ℕ) :
    (∫ h, pullsPlus a h / (pullsPlus a h + pullsPlus a' h) ∂(banditMeasure ν π T) =
      ∫ h, (pullsPlus a h / pullsPlus a' h) / (1 + pullsPlus a h / pullsPlus a' h)
        ∂(banditMeasure ν π T)) ∧
    (∫ h, (pullsPlus a h / pullsPlus a' h) / (1 + pullsPlus a h / pullsPlus a' h)
        ∂(banditMeasure ν π T) ≤
      (∫ h, pullsPlus a h / pullsPlus a' h ∂(banditMeasure ν π T)) /
        (1 + ∫ h, pullsPlus a h / pullsPlus a' h ∂(banditMeasure ν π T))) := by sorry

end ExploreFirst.Relative
