-- Prove2me | Theorems.Thm_FairKMeans_lemma_20
-- name    : FairKMeans.lemma_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:33:05.680339+00:00
-- url     : https://prove2.me/theorems/3ad561a4-790a-4704-817a-adb1d67218a7
-- title:
--   Lemma 20 — weighted-mean identity $\sum_p\sum_t\phi_T(p,t)\|\pi(t)-\nu_p\|^2=C_T-C_\nu$
-- statement:
--   For every relaxed solution $(T,\phi_T)$,
--
--   $$\sum_{p\in P}\sum_{t\in T}\phi_T(p,t)\|\pi(t)-\nu_p\|^2=C_T-C_\nu,\qquad C_\nu\le C_T. \tag{30}$$
--
--   The drift of a relaxed solution never exceeds its centroid cost.
--
--   Differences from the source:
--   - encoding: π(t) of a zero column (undefined) → Lean's 0⁻¹ • 0 = 0, always multiplied by the weight 0; reason: Lean convention; no sum changes
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Lemma 20, (30), p.27 (PDF p.29)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_RelaxedSolution

namespace FairKMeans

/-- **Lemma 20 (Weighted-mean identity)**, p.27 (PDF 29), (30). Cheng–Mo–Song–Ding,
arXiv:2609.07974 (held version, sha256 73e9312c…).

For every relaxed solution, `∑_p ∑_t φ_T(p,t)‖π(t) − ν_p‖² = C_T − C_ν` and `C_ν ≤ C_T`. -/
theorem lemma_20 {d n m s : ℕ} (I : Instance d n m) (φ : Fin n → Fin s → ℝ)
    (h : IsRelaxed I φ) :
    ∑ p, ∑ t, φ p t * ‖cen I φ t - nu I φ p‖ ^ 2 = CT I φ - Cnu I φ ∧
      Cnu I φ ≤ CT I φ := by sorry

end FairKMeans
