-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_spectral_estimate
-- name    : CorrelatedLocalSearch.spectral_estimate
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:06.208572+00:00
-- url     : https://prove2.me/theorems/b1f98ad4-c877-4c9d-bfe7-c88da6d53817
-- title:
--   Proof of Lemma C.1 — $\|B^{-1}R^{(m)}B\|_2\le\cos\frac{\pi}{2m-1}$ and $F_T(h)\le\frac{\lambda^h}{\sqrt{\lambda^2-1}}e^{-\pi^2T/(2(2m-1)^2)}$
-- statement:
--   Let $k/2<r<k$, $m\ge2$, $L=m-1$ and $B=\mathrm{diag}(\lambda,\lambda^2,\dots,\lambda^L)$. Then
--
--   1. for every vector $v$ on $\{1,\dots,L\}$, $\ \|B^{-1}R^{(m)}Bv\|_2\le\cos\frac{\pi}{2m-1}\,\|v\|_2$;
--   2. $\bigl\|(\lambda^{-j})_{j=1}^L\bigr\|_2\le 1/\sqrt{\lambda^2-1}$;
--   3. for $1\le h\le L$ and every $T\ge0$,
--   $$
--   F_T(h)\ \le\ \frac{\lambda^h}{\sqrt{\lambda^2-1}}\Bigl(\cos\frac{\pi}{2m-1}\Bigr)^T\ \le\ \frac{\lambda^h}{\sqrt{\lambda^2-1}}\exp\Bigl(-\frac{\pi^2T}{2(2m-1)^2}\Bigr).
--   $$
--
--   The decay on the time scale $m^2$ is what, balanced against the barrier cost $\lambda^{-m}$, gives the stretched-exponential tail $e^{-cT^{1/3}}$.
--
--   **Formalization Note** The Euclidean norm is written $\sqrt{\sum_i v_i^2}$ and the operator-norm bound is stated for every vector, which avoids choosing a matrix norm.
--
--   Differences from the source:
--   - encoding: integers k/2 < r < k → natural numbers k, r with k < 2r and r < k; reason: same instances
--   - encoding: ‖B⁻¹R^(m)B‖₂ ≤ cos(π/(2m−1)) → ‖B⁻¹R^(m)B v‖₂ ≤ cos(π/(2m−1))‖v‖₂ for every v; reason: definition of the operator norm
--   - encoding: L = m − 1 with a barrier m > h ≥ 1 → 2 ≤ m; reason: the paper's barrier has m ≥ 2; at m ≤ 1 the index set is empty
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), App. C.1, proof of Lemma C.1, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_sStar
import Definitions.Def_CorrelatedLocalSearch_reflMatrix

set_option autoImplicit false

namespace CorrelatedLocalSearch

/-- The spectral estimate (Xu, *Local Search with Correlated Randomness*, arXiv:2607.17469
(sha256 17e00d69…), App. C.1, proof of Lemma C.1, p.22): with `L = m − 1` and
`B = diag(λ, …, λ^L)`,
1. `‖B⁻¹ R^{(m)} B v‖₂ ≤ cos(π/(2m − 1)) ‖v‖₂` for every `v`;
2. `‖(λ^{−j})_{j=1}^L‖₂ ≤ 1/√(λ² − 1)`;
3. for `1 ≤ h ≤ L` and every `T`,
   `F_T(h) ≤ λ^h/√(λ²−1) · cos(π/(2m−1))^T ≤ λ^h/√(λ²−1) · exp(−π²T/(2(2m−1)²))`.

**Formalization Note** The operator-norm bound is stated pointwise for every vector, with the
Euclidean norm written as `√(Σ vᵢ²)`. Index `i : Fin (m − 1)` is the potential `i + 1`, so
`B` has entry `λ^{i+1}`. `F_T` is `reflF`. -/
theorem spectral_estimate (k r : ℕ) (hk : k < 2 * r) (hr : r < k) (m : ℕ) (hm : 2 ≤ m) :
    (∀ v : Fin (m - 1) → ℝ,
        Real.sqrt (∑ i, (((Matrix.diagonal (fun i : Fin (m - 1) => (lam k r ^ ((i : ℕ) + 1))⁻¹) *
            reflMatrix k r m * Matrix.diagonal (fun i : Fin (m - 1) => lam k r ^ ((i : ℕ) + 1))).mulVec
              v) i) ^ 2) ≤
          Real.cos (Real.pi / (2 * (m : ℝ) - 1)) * Real.sqrt (∑ i, v i ^ 2)) ∧
      Real.sqrt (∑ j : Fin (m - 1), ((lam k r ^ ((j : ℕ) + 1))⁻¹) ^ 2) ≤
        1 / Real.sqrt (lam k r ^ 2 - 1) ∧
      ∀ h T : ℕ, 1 ≤ h → h ≤ m - 1 →
        reflF k r m T h ≤
            lam k r ^ h / Real.sqrt (lam k r ^ 2 - 1) * Real.cos (Real.pi / (2 * (m : ℝ) - 1)) ^ T ∧
          lam k r ^ h / Real.sqrt (lam k r ^ 2 - 1) * Real.cos (Real.pi / (2 * (m : ℝ) - 1)) ^ T ≤
            lam k r ^ h / Real.sqrt (lam k r ^ 2 - 1) *
              Real.exp (-(Real.pi ^ 2 * T) / (2 * (2 * (m : ℝ) - 1) ^ 2)) := by sorry

end CorrelatedLocalSearch
