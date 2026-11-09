-- Prove2me | Theorems.Thm_CubeSampling_lemma_3_2
-- name    : CubeSampling.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:18:10.400404+00:00
-- url     : https://prove2.me/theorems/c8b0ed70-3333-4a10-beb3-37c10e6eeae2
-- title:
--   Lemma 3.2 — cancellation at the second moment term
-- statement:
--   **Lemma 3.2.** For every $q_0 < 1/2$ there is $C_0 < \infty$ such that, for $0 < q \le q_0$ and $0 \le s \le 1/2$,
--   $$
--   F(2 + 2s, q) \le s\,\Psi(q) + C_0\, q\, s^3. \tag{7}
--   $$
--   Consequently, if $\mathbb E[h^2] = 1$ and $\deg h \le k \le q_0 d$ (that is, $h \in P_{d,k}$), then for $0 \le s \le 1/2$
--   $$
--   \log \mathbb E\bigl[|h|^{2+2s}\bigr] \le s\,\Lambda_{d,k} + C_0\, k\, s^3. \tag{8}
--   $$
--
--   The point of the lemma is the absence of a quadratic error term in $s$; it gives the $k^{1/3}$ remainder of Proposition 3.3.
--
--   Differences from the source:
--   - encoding: z the unique root of the equation in (6) → z chosen by Classical.epsilon among the roots; reason: the paper asserts uniqueness, so the value is the paper's; existence is proved in the sanity file
--   - reading: (8) stated after (7) with 'Consequently' → (8) for 0 ≤ s ≤ 1/2, with the same C₀; reason: the range of s and the constant are those of (7), from which (8) follows
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Lemma 3.2, (7), (8), p.13

import Mathlib
import Definitions.Def_CubeSampling_lowDeg
import Definitions.Def_CubeSampling_cubeMean
import Definitions.Def_CubeSampling_ksF
import Definitions.Def_CubeSampling_Psi
import Definitions.Def_CubeSampling_Lambda

namespace CubeSampling

/-- Lemma 3.2 (cancellation at the second moment term) (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Lemma 3.2, p.13): for every
`q₀ < 1/2` there is `C₀ < ∞` with (7) `F(2 + 2s, q) ≤ sΨ(q) + C₀ q s³` for `0 < q ≤ q₀`, `0 ≤ s ≤ 1/2`, and
consequently (8) `log E[|h|^{2+2s}] ≤ sΛ_{d,k} + C₀ k s³` whenever `E[h²] = 1` and `deg h ≤ k ≤ q₀ d`.

**Formalization Note** One `C₀` serves (7) and (8); `s` ranges over `[0, 1/2]` in (8) as in (7). -/
theorem lemma_3_2 (q₀ : ℝ) (hq₀ : q₀ < 1 / 2) :
    ∃ C₀ : ℝ,
      (∀ q : ℝ, 0 < q → q ≤ q₀ → ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 →
        ksF (2 + 2 * s) q ≤ s * Psi q + C₀ * q * s ^ 3) ∧
      (∀ (d k : ℕ) (h : Cube d → ℝ), h ∈ lowDeg d k → cubeMean d (fun x => h x ^ 2) = 1 →
        (k : ℝ) ≤ q₀ * d → ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 →
        Real.log (cubeMean d (fun x => |h x| ^ (2 + 2 * s))) ≤ s * Lambda d k + C₀ * k * s ^ 3) := by sorry

end CubeSampling
