-- Prove2me | Theorems.Thm_DRBatchBandit_cover_FPi
-- name    : DRBatchBandit.cover_FPi
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:25:08.180259+00:00
-- url     : https://prove2.me/theorems/8c05b10d-9712-49cc-a778-c9b572efa3e3
-- title:
--   Proof of Theorem 2, p.54 — $N(t,\mathcal F_\Pi,\|\cdot\|_{\mathbf P_n})\le N_H^{(n)}(\eta^2t^2,\Pi)$
-- statement:
--   Assume overlap, $\pi_0(a\mid x)\ge\eta>0$. For any $n\ge1$ points $z_1,\dots,z_n$ (draws $(X_i,Y_i,A_i)$) and any $t>0$,
--   $$N\big(t,\mathcal F_\Pi,\|\cdot\|_{\mathbf P_n}\big)\le N_H^{(n)}(\eta^2t^2,\Pi),$$
--   where $\mathcal F_\Pi=\{\mathbf 1\{\pi(X)=A\}/\pi_0(A\mid X):\pi\in\Pi\}$ and $N_H^{(n)}$ is the $n$-point Hamming covering number of Definition 5.
--
--   It converts a covering of the policy class in Hamming distance into a covering of the weighted class $\mathcal F_\Pi$, the input to the chaining bound on $\mathcal R_n(\mathcal F_\Pi)$.
--
--   **Formalization Note** Proper covers on both sides, valued in $\mathbb N\cup\{\infty\}$.
--
--   Differences from the source:
--   - encoding: actions a¹, …, a^d → Fin d, 0-based; rewards a vector Fin d → ℝ; reason: Lean convention; no instance changes
--   - encoding: covering number N(t, ℱ, ‖·‖) → PlugInRisk.coveringNumber: proper cover (centres in ℱ), valued in ℕ∞, distances and scale mapped to [0, ∞] by ENNReal.ofReal; reason: the paper's covers are built from members of the class; ℕ∞ keeps an infinite covering number from collapsing to 0
--   - reading: a set of n points {x₁, …, x_n} in Definition 5 → a sequence x : Fin n → X (repetitions allowed); reason: the proof applies the definition to the sample X₁, …, X_n, which may repeat
--   - encoding: n data points → 1 ≤ n; reason: the paper's n is a sample size; n = 0 is not in its scope
-- source:
--   Si, Zhang, Zhou & Blanchet, Distributionally Robust Batch Contextual Bandits, arXiv:2006.05630v7, proof of Theorem 2, p.54 ("Therefore, the covering number"). PDF sha256 ac485985feb75d33b603f06f5a5d93c52077877db7be11de3d71107c7c374b02

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Setting
import Definitions.Def_DRBatchBandit_Assumptions
import Definitions.Def_DRBatchBandit_EntropyIntegral
import Definitions.Def_PlugInRisk_coveringNumber
import Definitions.Def_DRBatchBandit_Covering
import Definitions.Def_DRBatchBandit_FunctionClasses

namespace DRBatchBandit

open OfflinePolicyLearning.Regret

/-- Proof of Theorem 2 (Si, Zhang, Zhou & Blanchet, arXiv:2006.05630v7, p.54, "Therefore, the
covering number"): under overlap, the covering number of `ℱ_Π` in the empirical distance on any
`n` points satisfies `N(t, ℱ_Π, ‖·‖_{P_n}) ≤ N_H⁽ⁿ⁾(η²t², Π)`.

**Formalization Note.** Covering numbers are the published `PlugInRisk.coveringNumber`
(proper covers, `ℕ∞`-valued) for the distances `ENNReal.ofReal ∘ empDist z` and
`ENNReal.ofReal ∘ L2Dist P` at scale `ENNReal.ofReal t`. Proper covers on both sides; the `n` points are any draws
`z : Fin n → Draw X d`; `t > 0`, `n ≥ 1`. -/
theorem cover_FPi {X : Type*} [MeasurableSpace X] {d : ℕ} (M : Model X d) (η : ℝ)
    (hov : Overlap M η) (Pol : Set (X → Fin d)) (n : ℕ) (hn : 1 ≤ n) (z : Fin n → Draw X d)
    (t : ℝ) (ht : 0 < t) :
    PlugInRisk.coveringNumber (fun f g => ENNReal.ofReal (empDist z f g)) (FPi M Pol)
        (ENNReal.ofReal t) ≤ hammingCoverNumN n (η ^ 2 * t ^ 2) Pol := by sorry

end DRBatchBandit
