-- Prove2me | Theorems.Thm_CoVaRMC_Batching_eq_32
-- name    : CoVaRMC.Batching.eq_32
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:00.504136+00:00
-- url     : https://prove2.me/theorems/60777901-1223-4b2a-b299-a0e3d7bf1b0e
-- title:
--   Proof of Theorem 3, p. 32, after Equation (32) — c_{m,k}(t) = −t + o(1) + O(√k/m)
-- statement:
--   Work under the hypotheses of Theorem 3 without any condition on $\sqrt k/m$, and let $c_{m,k}(t) = \frac{\sqrt k}{\hat\sigma(y_k)}\big(\beta - \mathrm E[I\{\hat Y \le y_k\}]\big)$ with $y_k = \mathrm{CoVaR}_{\alpha,\beta} + tAk^{-1/2}$ as in Equation (30). For every $t \in \mathbb R$,
--   $$c_{m,k}(t) = -t + o(1) + O\big(\sqrt k/m\big) \qquad (n \to \infty):$$
--   there are a sequence $g_n \to 0$ and a constant $C$ such that $|c_{m,k}(t) + t - g_n| \le C\sqrt k/m$ for all sufficiently large $n$.
--
--   Combined with Equation (31), this yields the normal limit when $\sqrt k/m \to 0$ and boundedness in probability at rate $k^{-1/2}$ when $\sqrt k/m$ converges to a nonzero constant.
--
--   **Formalization Note.** The sequence is indexed by $\nu$ with $n = k(\nu)m(\nu)$; $o(1)$ is a sequence tending to $0$ and $O(\sqrt k/m)$ is "eventually bounded by $C\sqrt k/m$".
-- source:
--   Huang, Lin, Hong, Monte-Carlo Estimation of CoVaR, arXiv:2210.06148v1, p. 32, proof of Theorem 3, the sentence after Equation (32)

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaRMC.Batching

/-- Proof of Theorem 3, p. 32, after Equation (32): `c_{m,k}(t) = -t + o(1) + O(√k/m)`. -/
theorem eq_32 (D : JointDensity) (Fc : ℝ → ℝ → ℝ) (α β : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (v c : ℝ) (𝒳 𝒴 : Set ℝ) (hFc : IsCondCDFVersion D Fc) (hA1 : Assumption1 D Fc v c 𝒳 𝒴)
    (hv : D.FX v = α) (hc : Fc c v = β)
    (M : ℝ) (hM : 0 < M)
    (hM1 : ∀ y ∈ 𝒴, |deriv (fun x => Fc y x) v| ≤ M)
    (hM2 : ∀ x : ℝ, ∀ y ∈ 𝒴, |deriv (deriv (fun x => Fc y x)) x| ≤ M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ × ℕ → Ω → ℝ × ℝ) (hSm : ∀ p, Measurable (S p)) (hSi : iIndepFun S P)
    (hSl : ∀ p, P.map (S p) = D.law)
    (k m : ℕ → ℕ) (hk0 : ∀ ν, 0 < k ν) (hm0 : ∀ ν, 0 < m ν)
    (hk : Tendsto k atTop atTop) (hm : Tendsto m atTop atTop)
    (t : ℝ) :
    ∃ (g : ℕ → ℝ) (C : ℝ), Tendsto g atTop (𝓝 0) ∧
      ∀ᶠ ν in atTop, |cmk P S α β c (Aconst D β v c) t (k ν) (m ν) + t - g ν| ≤ C * √(k ν : ℝ) / m ν := by sorry

end CoVaRMC.Batching
