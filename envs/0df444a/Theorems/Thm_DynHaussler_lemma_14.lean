-- Prove2me | Theorems.Thm_DynHaussler_lemma_14
-- name    : DynHaussler.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:36:32.208481+00:00
-- url     : https://prove2.me/theorems/4e7ffe53-d20d-47e0-8d0b-0b9885924fbf
-- title:
--   Lemma 14 — schedule-count estimates (36)–(38)
-- statement:
--   For integers $m,r\ge1$,
--   $$
--   Q_r(m)\le 2^r\binom{m+r}{r}\le\Bigl[2e\Bigl(1+\frac mr\Bigr)\Bigr]^r. \tag{36}
--   $$
--   For every integer $\ell\ge0$,
--   $$
--   \sum_{i=0}^{\ell}n_i(m)\,n_{\ell-i}(m)=n_\ell(2m). \tag{37}
--   $$
--   Consequently, for every integer $d\ge1$,
--   $$
--   \sum_{i=0}^{d-1}n_i(m)\,Q_{d-i}(m)\le Q_d(2m). \tag{38}
--   $$
--
--   The size estimate handles the short-horizon regime directly, and the convolution identity counts continuation capacity in the routing construction.
--
--   **Formalization Note** $e$ is $\exp(1)$. Identity (37) and inequality (38) are stated for every $m\ge0$.
--
--   Differences from the source:
--   - generalization: (37), (38) for integers m ≥ 1 → (37), (38) for every m ≥ 0; reason: at m = 0 they read [ℓ = 0] = [ℓ = 0] and 1 ≤ 1; the cases m ≥ 1 are the source's
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 14, Eqs. (36)–(38), p.21 (PDF p.23)

import Mathlib
import Definitions.Def_DynHaussler_QCount

set_option autoImplicit false

namespace DynHaussler

/-- **Lemma 14 (Schedule-count estimates).** For integers `m, r ≥ 1`,
`Q_r(m) ≤ 2^r binom(m + r, r) ≤ [2e(1 + m/r)]^r` (Eq. (36)). For every integer `ℓ ≥ 0`,
`∑_{i=0}^ℓ n_i(m) n_{ℓ−i}(m) = n_ℓ(2m)` (Eq. (37)). Consequently, for every integer `d ≥ 1`,
`∑_{i=0}^{d−1} n_i(m) Q_{d−i}(m) ≤ Q_d(2m)` (Eq. (38)).
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 14, Eqs. (36)–(38), p.21 (PDF p.23).

**Formalization Note** `e` is `Real.exp 1`. (37) and (38) are stated for every `m ≥ 0`; at `m = 0`
they read `[ℓ = 0] = [ℓ = 0]` and `1 ≤ 1`. -/
theorem lemma_14 :
    (∀ m r : ℕ, 1 ≤ m → 1 ≤ r →
      (QCount r m : ℝ) ≤ 2 ^ r * (Nat.choose (m + r) r : ℝ) ∧
      2 ^ r * (Nat.choose (m + r) r : ℝ) ≤ (2 * Real.exp 1 * (1 + (m : ℝ) / r)) ^ r) ∧
    (∀ m ℓ : ℕ, ∑ i ∈ Finset.range (ℓ + 1), nCount i m * nCount (ℓ - i) m = nCount ℓ (2 * m)) ∧
    (∀ m d : ℕ, 1 ≤ d →
      ∑ i ∈ Finset.range d, nCount i m * QCount (d - i) m ≤ QCount d (2 * m)) := by sorry

end DynHaussler
