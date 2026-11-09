-- Prove2me | Theorems.Thm_DerandSq_lemma_2_2
-- name    : DerandSq.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:53:31.295563+00:00
-- url     : https://prove2.me/theorems/586cdfd8-cd23-4b85-8544-21143b363b65
-- title:
--   Lemma 2.2 ([NS06], Proposition 3.17) — $\|a\| = \lim_{k\to\infty} \tau((a^*a)^k)^{1/2k}$ for a faithful trace
-- statement:
--   Let $(\mathcal A, \tau)$ be a **C\*-probability space** (Definition 2.1): $\mathcal A$ is a unital C\*-algebra and $\tau : \mathcal A \to \mathbb C$ is a linear functional with
--   1. $\tau(1_{\mathcal A}) = 1$,
--   2. $\tau(ab) = \tau(ba)$ for all $a, b$ (a trace),
--   3. $\tau(a^*a) \geq 0$ for all $a$ (positive).
--
--   Suppose $\tau$ is **faithful**: $\tau(a^*a) = 0$ implies $a = 0$. Then for every $a \in \mathcal A$,
--   $$
--   \|a\| = \lim_{k \to \infty} \Bigl(\tau\bigl((a^*a)^k\bigr)\Bigr)^{1/(2k)} .
--   $$
--   This is the moment formula for the norm that turns the computation of $\|Q_H(u)\|_{C^*_{\mathrm{red}}(\Gamma_d)}$ into the counting of closed walks (Proposition 4.6).
--
--   Differences from the source:
--   - reading: lim_{p→∞} (τ((a*a)^k))^{1/2k} (limit variable p, exponent index k) → one index k → ∞; reason: the printed formula mixes two letters for one index; the use in Proposition 4.6 reads lim_p τ((s*s)^p)^{1/2p}
--   - encoding: τ((a*a)^k)^{1/2k} → real part of τ((a*a)^k), raised to the real power 1/(2k); reason: (a*a)^k is a positive element c*c (c = (a*a)^{k/2} by functional calculus), so τ of it is a nonnegative real by positivity
--   - encoding: τ(a*a) ≥ 0 → 0 ≤ τ(a*a) in ℂ's partial order (real and nonnegative); reason: the meaning of ≥ 0 for a complex number
--   - encoding: unital C*-algebra → Mathlib's CStarAlgebra (unital, complete, ‖a*a‖ = ‖a‖², normed ℂ-algebra); reason: the standard notion of Definition 2.1
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), Lemma 2.2, p.8 (with Definition 2.1, p.8)

import Mathlib
open scoped ComplexOrder

namespace DerandSq

/-- Lemma 2.2 ([NS06], Proposition 3.17) of Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), p.8. Let `(A, τ)` be a C*-probability space
(Definition 2.1, p.8: `A` a unital C*-algebra, `τ : A → ℂ` linear with `τ(1) = 1`, a trace
`τ(ab) = τ(ba)`, positive `τ(a*a) ≥ 0`) such that `τ` is faithful (`τ(a*a) = 0` implies `a = 0`).
Then for every `a ∈ A`, `‖a‖ = lim_{k → ∞} τ((a*a)^k)^{1/(2k)}`.

**Formalization Note** The printed limit variable is `p` while the exponent uses `k`; read with one
index `k`. `τ((a*a)^k)` is a nonnegative real (`(a*a)^k = b*b`), so its real part is taken before
the real power; positivity `τ(a*a) ≥ 0` is in `ℂ`'s partial order (real and nonnegative). -/
theorem lemma_2_2 {A : Type*} [CStarAlgebra A] (τ : A →ₗ[ℂ] ℂ) (hτ1 : τ 1 = 1)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a)) (hpos : ∀ a : A, 0 ≤ τ (star a * a))
    (hfaith : ∀ a : A, τ (star a * a) = 0 → a = 0) (a : A) :
    Filter.Tendsto (fun k : ℕ => (τ ((star a * a) ^ k)).re ^ ((1 : ℝ) / (2 * k)))
      Filter.atTop (nhds ‖a‖) := by sorry

end DerandSq
