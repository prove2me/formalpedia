-- Prove2me | Theorems.Thm_EffRobustLearn_lemma_3_7
-- name    : EffRobustLearn.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:38:10.916195+00:00
-- url     : https://prove2.me/theorems/bedd380d-b709-4cf0-b38b-ddb500f87a44
-- title:
--   Lemma 3.7 — bound on $\|g_t\|_2$
-- statement:
--   For nonempty samples and $[-1,1]$-valued $\bar\mu$ and $h$, the vector $g$ of (3.6) satisfies
--   $$\|g\|_2\le\sqrt{\frac1{4|\bar S_{\mathrm{inp}}|}+\frac9{16|S_{\mathrm{ref}}|}}.$$
--
--   This is the gradient bound the regret analysis needs.
--
--   Differences from the source:
--   - generalization: $\bar\mu_t\in\mathrm{conv}(C)$, $h_t=\mathrm{maj}_k\circ\bar\mu_t$ → every $[-1,1]$-valued $\bar\mu$ and $h$; reason: the source's pairs are $[-1,1]$-valued and the proof uses nothing else
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Lemma 3.7, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_EffRobustLearn_gVec

namespace EffRobustLearn

/-- Lemma 3.7 (Gradient bound), p.15 (arXiv:2609.17655, held version, sha256 312a0857…): `‖g‖₂ ≤ √(1/(4|S̄inp|) + 9/(16|Sref|))`.

**Formalization Note.** Stated for arbitrary `[-1, 1]`-valued `μ̄` and `h`, which contains `μ̄_t ∈ conv(C)` and `h_t = maj_k ∘ μ̄_t`. -/
theorem lemma_3_7 {X : Type*} {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (μ h : X → ℝ)
    (hμ : ∀ x, |μ x| ≤ 1) (hh : ∀ x, |h x| ≤ 1) (Sinp : Fin n → X × Bool) (Sref : Fin m → X) :
    ‖gVec μ h Sinp Sref‖ ≤ Real.sqrt (1 / (4 * (n : ℝ)) + 9 / (16 * (m : ℝ))) := by sorry

end EffRobustLearn
