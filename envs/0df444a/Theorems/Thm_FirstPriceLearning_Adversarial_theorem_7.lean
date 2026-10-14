-- Prove2me | Theorems.Thm_FirstPriceLearning_Adversarial_theorem_7
-- name    : FirstPriceLearning.Adversarial.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:58.724105+00:00
-- url     : https://prove2.me/theorems/331cd4c1-8277-420b-a9bc-3a41218c1c4d
-- title:
--   Theorem 7 — $\mathbb E[R_T(\pi^{\mathrm{ML\text{-}IS\text{-}UCB}};v)]\le4+(L+4)\lceil\sqrt T\rceil+80\gamma^{3/2}\log(LKT)(1+\log T)L\sqrt T$
-- statement:
--   Let the private values $v_1,\dots,v_T\in[0,1]$ be a sequence chosen by an oblivious adversary, and let the HOBs be iid with a CDF $G$ on $[0,1]$. For every tuning parameter $\gamma\ge3$ and every selection rule, the regret of the ML-IS-UCB policy (Algorithm 4) satisfies
--   $$
--   \mathbb E\big[R_T(\pi^{\mathrm{ML\text{-}IS\text{-}UCB}};v)\big]\le4+(L+4)\cdot\lceil\sqrt T\rceil+80\gamma^{3/2}\log(LKT)(1+\log T)\cdot L\sqrt T,
--   $$
--   where $L=\lceil\log_2T\rceil$, $K=\lceil\sqrt T\rceil$, $R_T$ is the regret (3) against the best bid in $[0,1]$, and the expectation is over the HOBs.
--
--   This is the explicit regret guarantee of the ML-IS-UCB policy; it gives the $\widetilde O(\sqrt T)$ bound of Theorem 2.
--
--   **Formalization Note** The paper prints "$v_1,\cdots,v_t$" and "$R(\pi^{\mathrm{ML\text{-}IS\text{-}UCB}};v)$" for $v_1,\dots,v_T$ and $R_T$ (slip 12). The statement holds for every $T\ge0$ (for $T\le1$ the right-hand side is at least $4$ and the regret is at most $T$), so no lower bound on $T$ is assumed. The conclusion also asserts integrability of the regret, so that the Bochner integral is the expectation. The policy is deterministic given the selection rule, so the expectation is over $m\sim G^{\otimes T}$ only.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 30, Theorem 7

import Mathlib
import Definitions.Def_FirstPriceLearning_Adversarial_Model
import Definitions.Def_FirstPriceLearning_Adversarial_MLISUCB

open MeasureTheory

namespace FirstPriceLearning.Adversarial

/-- Theorem 7, p. 30: for every horizon `T`, every `γ ≥ 3`, every selection rule, every oblivious
value sequence `v ∈ [0,1]^T` and every HOB law `G` on `[0, 1]`, the regret of ML-IS-UCB is
integrable and
`𝔼[R_T(π^{ML-IS-UCB}; v)] ≤ 4 + (L + 4)⌈√T⌉ + 80 γ^{3/2} log(LKT)(1 + log T) · L √T`,
with `L = ⌈log₂ T⌉` and `K = ⌈√T⌉`; the expectation is over the iid HOBs `m_t ∼ G`. -/
theorem theorem_7 (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (hsel : IsSelectionRule sel) (v : Fin T → ℝ) (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1)
    (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    Integrable (fun m => regret μG v (mlBids T γ sel v m)) (Measure.pi fun _ : Fin T => μG) ∧
    ∫ m, regret μG v (mlBids T γ sel v m) ∂(Measure.pi fun _ : Fin T => μG)
      ≤ 4 + ((numLevels T : ℝ) + 4) * (numGrid T : ℝ)
          + 80 * γ ^ ((3 : ℝ) / 2) * logFactor T * (1 + Real.log T) * (numLevels T : ℝ)
            * Real.sqrt T := by sorry

end FirstPriceLearning.Adversarial
