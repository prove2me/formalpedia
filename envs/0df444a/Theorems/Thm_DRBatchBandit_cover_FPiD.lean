-- Prove2me | Theorems.Thm_DRBatchBandit_cover_FPiD
-- name    : DRBatchBandit.cover_FPiD
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:25:19.661787+00:00
-- url     : https://prove2.me/theorems/de6d674a-b546-49cf-b877-286d47fba00a
-- title:
--   Proof of Theorem 2, p.56 — $N(t,\mathcal F_{\Pi,\mathbb D},\|\cdot\|_{\mathbf P_n})\le N_H^{(n)}(\eta^2t^2/2,\Pi)\,2^{|\mathbb D|}$
-- statement:
--   Assume overlap, $\pi_0(a\mid x)\ge\eta>0$, and let $\mathbb D$ be a finite set. For any $n\ge1$ points $z_1,\dots,z_n$ and any $t>0$,
--   $$N\big(t,\mathcal F_{\Pi,\mathbb D},\|\cdot\|_{\mathbf P_n}\big)\le N_H^{(n)}(\eta^2t^2/2,\Pi)\,2^{|\mathbb D|},$$
--   where $\mathcal F_{\Pi,\mathbb D}=\{\mathbf 1\{\pi(X)=A\}\mathbf 1\{Y(\pi(X))\in S\}/\pi_0(A\mid X):\pi\in\Pi,\ S\subset\mathbb D\}$.
--
--   It is the covering input to the discrete case of Theorem 2.
--
--   **Formalization Note** Proper covers, valued in $\mathbb N\cup\{\infty\}$; $S$ ranges over all subsets of $\mathbb D$.
--
--   Differences from the source:
--   - encoding: actions a¹, …, a^d → Fin d, 0-based; rewards a vector Fin d → ℝ; reason: Lean convention; no instance changes
--   - encoding: covering number N(t, ℱ, ‖·‖) → PlugInRisk.coveringNumber: proper cover (centres in ℱ), valued in ℕ∞, distances and scale mapped to [0, ∞] by ENNReal.ofReal; reason: the paper's covers are built from members of the class; ℕ∞ keeps an infinite covering number from collapsing to 0
--   - reading: a set of n points {x₁, …, x_n} in Definition 5 → a sequence x : Fin n → X (repetitions allowed); reason: the proof applies the definition to the sample X₁, …, X_n, which may repeat
--   - encoding: n data points → 1 ≤ n; reason: the paper's n is a sample size; n = 0 is not in its scope
-- source:
--   Si, Zhang, Zhou & Blanchet, Distributionally Robust Batch Contextual Bandits, arXiv:2006.05630v7, proof of Theorem 2, p.56 ("Now, we turn to the Rademacher complexity of the classes FΠ,D. We claim"). PDF sha256 ac485985feb75d33b603f06f5a5d93c52077877db7be11de3d71107c7c374b02

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Setting
import Definitions.Def_DRBatchBandit_Assumptions
import Definitions.Def_DRBatchBandit_EntropyIntegral
import Definitions.Def_PlugInRisk_coveringNumber
import Definitions.Def_DRBatchBandit_Covering
import Definitions.Def_DRBatchBandit_FunctionClasses

namespace DRBatchBandit

open OfflinePolicyLearning.Regret

/-- Proof of Theorem 2 (Si, Zhang, Zhou & Blanchet, arXiv:2006.05630v7, p.56, "Now, we turn to
the Rademacher complexity of the classes FΠ,D. We claim"): under overlap,
`N(t, ℱ_{Π,𝔻}, ‖·‖_{P_n}) ≤ N_H⁽ⁿ⁾(η²t²/2, Π) 2^{|𝔻|}`.

**Formalization Note.** Covering numbers are the published `PlugInRisk.coveringNumber`
(proper covers, `ℕ∞`-valued) for the distances `ENNReal.ofReal ∘ empDist z` and
`ENNReal.ofReal ∘ L2Dist P` at scale `ENNReal.ofReal t`. Proper covers; arithmetic in `ℕ∞`; the `n` points are any draws
`z : Fin n → Draw X d`; `t > 0`, `n ≥ 1`; `𝔻` is a `Finset ℝ` and `S` ranges over its
subsets. -/
theorem cover_FPiD {X : Type*} [MeasurableSpace X] {d : ℕ} (M : Model X d) (η : ℝ)
    (hov : Overlap M η) (Pol : Set (X → Fin d)) (D : Finset ℝ) (n : ℕ) (hn : 1 ≤ n)
    (z : Fin n → Draw X d) (t : ℝ) (ht : 0 < t) :
    PlugInRisk.coveringNumber (fun f g => ENNReal.ofReal (empDist z f g)) (FPiD M Pol D)
        (ENNReal.ofReal t) ≤ hammingCoverNumN n (η ^ 2 * t ^ 2 / 2) Pol * 2 ^ D.card := by sorry

end DRBatchBandit
