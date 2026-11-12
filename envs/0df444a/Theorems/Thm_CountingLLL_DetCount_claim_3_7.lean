-- Prove2me | Theorems.Thm_CountingLLL_DetCount_claim_3_7
-- name    : CountingLLL.DetCount.claim_3_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:33.844831+00:00
-- url     : https://prove2.me/theorems/b98c6bf6-0b94-462c-b100-1e4dab7dee02
-- title:
--   Claim 3.7 — sensitivity of reciprocal products
-- statement:
--   Let $0<t<1$ and $\ell\ge1$, and let $(x_i)_{i\in[\ell]},(y_i)_{i\in[\ell]}\in[-t,t]^\ell$. Then
--   $$\Big|\prod_{i=1}^{\ell}\frac{1}{1-x_i}-\prod_{i=1}^{\ell}\frac{1}{1-y_i}\Big|\le\frac{\ell}{(1-t)^{\ell+1}}\cdot\max_{1\le i\le\ell}|x_i-y_i|.$$
--
--   This elementary estimate converts errors in the recursive marginals into errors in the expansion (14).
--
--   Differences from the source:
--   - encoding: indices 1 ≤ i ≤ ℓ → indices in Fin ℓ (0-based); reason: relabelling
-- source:
--   Hongyang Liu, Chunyang Wang, Yitong Yin, Yiyao Zhang, Can Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442 (October 2026), Claim 3.7, equation (17), PDF p. 11 (printed p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib

set_option autoImplicit false

namespace CountingLLL.DetCount

/-- Claim 3.7: for `0 < t < 1`, `ℓ ≥ 1` and `x, y ∈ [−t, t]^ℓ`,
`|∏_{i=1}^ℓ 1/(1 − x_i) − ∏_{i=1}^ℓ 1/(1 − y_i)| ≤ ℓ/(1 − t)^{ℓ+1} · max_i |x_i − y_i|`. -/
theorem claim_3_7 (t : ℝ) (ht₀ : 0 < t) (ht₁ : t < 1) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (x y : Fin ℓ → ℝ) (hx : ∀ i, x i ∈ Set.Icc (-t) t) (hy : ∀ i, y i ∈ Set.Icc (-t) t) :
    |∏ i, 1 / (1 - x i) - ∏ i, 1 / (1 - y i)| ≤
      (ℓ : ℝ) / (1 - t) ^ (ℓ + 1) *
        (Finset.univ : Finset (Fin ℓ)).sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hℓ⟩⟩)
          (fun i => |x i - y i|) := by sorry

end CountingLLL.DetCount
