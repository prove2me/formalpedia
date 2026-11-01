-- Prove2me | Theorems.Thm_DRBatchBandit_cover_FI_uniform
-- name    : DRBatchBandit.cover_FI_uniform
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:24:42.97598+00:00
-- url     : https://prove2.me/theorems/a8f9e652-7521-4648-b4fa-2952ae8d886a
-- title:
--   Proof of Theorem 2, p.55 (van der Vaart 19.15–19.16) — $\sup_{\mathbf P}N(t,\mathcal F_I,\|\cdot\|_{\mathbf P})\le K/t^2$ (corrected: $0<t\le1$)
-- statement:
--   There is a universal constant $K$ such that for every $M\ge0$, every probability measure $\mathbf P$ on $\mathbb R$ and every $0<t\le1$,
--   $$N\big(t,\mathcal F_I,\|\cdot\|_{\mathbf P}\big)\le K\Big(\frac1t\Big)^2,$$
--   where $\mathcal F_I=\{\mathbf 1\{\cdot\le x\}:x\in[0,M]\}$ is the class of half-line indicators.
--
--   The paper quotes this from van der Vaart, *Asymptotic Statistics*, Lemma 19.15 and Example 19.16. It makes the entropy integral of $\mathcal F_I$ finite and independent of $\mathbf P$.
--
--   **Formalization Note** $K$ is chosen before $M$, $\mathbf P$ and $t$. Proper covers, valued in $\mathbb N\cup\{\infty\}$ and compared in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: covering number N(t, ℱ, ‖·‖) → PlugInRisk.coveringNumber: proper cover (centres in ℱ), valued in ℕ∞, distances and scale mapped to [0, ∞] by ENNReal.ofReal; reason: the paper's covers are built from members of the class; ℕ∞ keeps an infinite covering number from collapsing to 0
--   - correction: sup_P N(t, ℱ_I, ‖·‖_P) ≤ K(1/t)² for all t > 0 → for 0 < t ≤ 1; reason: false for large t: for t > √K the right side is < 1 while a nonempty class has covering number ≥ 1 (e.g. M = 0, any P); the cited van der Vaart lemma is stated for ε < 1
--   - encoding: M the reward bound → every Mrew ≥ 0; reason: the paper's M ≥ 0; K must not depend on M
-- source:
--   Si, Zhang, Zhou & Blanchet, Distributionally Robust Batch Contextual Bandits, arXiv:2006.05630v7, proof of Theorem 2, p.55 ("From Lemma 19.15 and Example 19.16 in [79], we know"). PDF sha256 ac485985feb75d33b603f06f5a5d93c52077877db7be11de3d71107c7c374b02

import Mathlib
import Definitions.Def_PlugInRisk_coveringNumber
import Definitions.Def_DRBatchBandit_Covering
import Definitions.Def_DRBatchBandit_FunctionClasses

open MeasureTheory

namespace DRBatchBandit

/-- Proof of Theorem 2 (Si, Zhang, Zhou & Blanchet, arXiv:2006.05630v7, p.55, "From Lemma 19.15
and Example 19.16 in [79], we know"): `sup_P N(t, ℱ_I, ‖·‖_P) ≤ K (1/t)²` with `K` a universal
constant.

**Formalization Note.** Corrected to `0 < t ≤ 1`: for `t > √K` the printed bound is `< 1`, but
a nonempty class has covering number `≥ 1`; the cited van der Vaart lemma is for `ε < 1`. `K` is
chosen before `M` and `P`. Covering number: the published `PlugInRisk.coveringNumber` (proper cover, `ℕ∞`, coerced to
`ℝ≥0∞`) for the distance `ENNReal.ofReal ∘ L2Dist P` at scale `ENNReal.ofReal t`. -/
theorem cover_FI_uniform :
    ∃ K : ℝ, ∀ Mrew : ℝ, 0 ≤ Mrew → ∀ P : ProbabilityMeasure ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 →
      ((PlugInRisk.coveringNumber (fun f g => ENNReal.ofReal (L2Dist (P : Measure ℝ) f g))
        (FI Mrew) (ENNReal.ofReal t) : ℕ∞) : ENNReal) ≤ ENNReal.ofReal (K * (1 / t) ^ 2) := by sorry

end DRBatchBandit
