-- Prove2me | Theorems.Thm_DRBatchBandit_cover_FPix
-- name    : DRBatchBandit.cover_FPix
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:25:11.862601+00:00
-- url     : https://prove2.me/theorems/21c3ac12-d907-44ad-8a5a-fc38c831528e
-- title:
--   Proof of Theorem 2, p.54 — $N(t,\mathcal F_{\Pi,x},\|\cdot\|_{\mathbf P_n})\le N_H^{(n)}(\eta^2t^2/2,\Pi)\sup_{\mathbf P}N(\eta t/\sqrt2,\mathcal F_I,\|\cdot\|_{\mathbf P})$
-- statement:
--   Assume overlap, $\pi_0(a\mid x)\ge\eta>0$. For any $n\ge1$ points $z_1,\dots,z_n$ and any $t>0$,
--   $$N\big(t,\mathcal F_{\Pi,x},\|\cdot\|_{\mathbf P_n}\big)\le N_H^{(n)}(\eta^2t^2/2,\Pi)\ \sup_{\mathbf P}N\big(\eta t/\sqrt2,\mathcal F_I,\|\cdot\|_{\mathbf P}\big),$$
--   where $\mathcal F_{\Pi,x}=\{\mathbf 1\{\pi(X)=A\}\mathbf 1\{Y(\pi(X))\le x\}/\pi_0(A\mid X):\pi\in\Pi,\ x\in[0,M]\}$, $\mathcal F_I=\{\mathbf 1\{\cdot\le x\}:x\in[0,M]\}$, and the supremum is over all probability measures $\mathbf P$ on $\mathbb R$.
--
--   It splits the covering of $\mathcal F_{\Pi,x}$ into a covering of the policy class and a uniform covering of half-line indicators, for the continuous case of Theorem 2.
--
--   **Formalization Note** Proper covers; the product and supremum are in $\mathbb N\cup\{\infty\}$.
--
--   Differences from the source:
--   - encoding: actions a¹, …, a^d → Fin d, 0-based; rewards a vector Fin d → ℝ; reason: Lean convention; no instance changes
--   - encoding: covering number N(t, ℱ, ‖·‖) → PlugInRisk.coveringNumber: proper cover (centres in ℱ), valued in ℕ∞, distances and scale mapped to [0, ∞] by ENNReal.ofReal; reason: the paper's covers are built from members of the class; ℕ∞ keeps an infinite covering number from collapsing to 0
--   - reading: a set of n points {x₁, …, x_n} in Definition 5 → a sequence x : Fin n → X (repetitions allowed); reason: the proof applies the definition to the sample X₁, …, X_n, which may repeat
--   - encoding: n data points → 1 ≤ n; reason: the paper's n is a sample size; n = 0 is not in its scope
-- source:
--   Si, Zhang, Zhou & Blanchet, Distributionally Robust Batch Contextual Bandits, arXiv:2006.05630v7, proof of Theorem 2, p.54 ("For the class FΠ,x, we claim"). PDF sha256 ac485985feb75d33b603f06f5a5d93c52077877db7be11de3d71107c7c374b02

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Setting
import Definitions.Def_DRBatchBandit_Assumptions
import Definitions.Def_DRBatchBandit_EntropyIntegral
import Definitions.Def_PlugInRisk_coveringNumber
import Definitions.Def_DRBatchBandit_Covering
import Definitions.Def_DRBatchBandit_FunctionClasses

open MeasureTheory

namespace DRBatchBandit

open OfflinePolicyLearning.Regret

/-- Proof of Theorem 2 (Si, Zhang, Zhou & Blanchet, arXiv:2006.05630v7, p.54, "For the class
F_{Π,x}, we claim"): under overlap,
`N(t, ℱ_{Π,x}, ‖·‖_{P_n}) ≤ N_H⁽ⁿ⁾(η²t²/2, Π) · sup_P N(ηt/√2, ℱ_I, ‖·‖_P)`,
the supremum over all probability measures `P` on `ℝ`.

**Formalization Note.** Covering numbers are the published `PlugInRisk.coveringNumber`
(proper covers, `ℕ∞`-valued) for the distances `ENNReal.ofReal ∘ empDist z` and
`ENNReal.ofReal ∘ L2Dist P` at scale `ENNReal.ofReal t`. Proper covers; arithmetic in `ℕ∞`; the `n` points are any draws
`z : Fin n → Draw X d`; `t > 0`, `n ≥ 1`. -/
theorem cover_FPix {X : Type*} [MeasurableSpace X] {d : ℕ} (M : Model X d) (η : ℝ)
    (hov : Overlap M η) (Pol : Set (X → Fin d)) (Mrew : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (z : Fin n → Draw X d) (t : ℝ) (ht : 0 < t) :
    PlugInRisk.coveringNumber (fun f g => ENNReal.ofReal (empDist z f g)) (FPix M Pol Mrew)
        (ENNReal.ofReal t) ≤
      hammingCoverNumN n (η ^ 2 * t ^ 2 / 2) Pol *
        ⨆ P : ProbabilityMeasure ℝ, PlugInRisk.coveringNumber
          (fun f g => ENNReal.ofReal (L2Dist (P : Measure ℝ) f g)) (FI Mrew)
          (ENNReal.ofReal (η * t / Real.sqrt 2)) := by sorry

end DRBatchBandit
