-- Prove2me | Theorems.Thm_ExitSpirals_lemma_8
-- name    : ExitSpirals.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:01:23.973735+00:00
-- url     : https://prove2.me/theorems/516db8bb-682f-47d1-bd59-c57e843fc34b
-- title:
--   Lemma 8 (corrected: continuity needs $q_1<1$) — the smallest root $f(s)$ of $f=H(1-s+sf)$ is decreasing and continuous
-- statement:
--   Let $q=(q_j)_{j\ge0}$ be a probability sequence with generating function $H(z)=\sum_jq_jz^j$, and let $f(s)$ be the smallest solution in $[0,1]$ of
--   $$f=H(1-s+s\,f),\qquad s\in[0,1].$$
--   Then
--
--   1. $f$ is (weakly) decreasing on $[0,1]$;
--   2. if $q_1<1$, $f$ is continuous on $[0,1]$.
--
--   Here $s$ plays the role of the paper's $x$: $1-s$ is the fraction of nodes removed. Applied to the link-origin law $p^-$ of either market, this controls the extinction probability entering $g$.
--
--   Differences from the source:
--   - correction: continuity on all of [0, 1] → continuity under the exclusion of the point mass at 1 (q_1 < 1, resp. p⁻_1 < 1); reason: for q = δ_1, H(z) = z: f(s) = 1 for s < 1 and f(1) = 0, so f, g and F jump at s = 1 (proved in the verification file)
--   - generalization: H the generating function of the branching law of a degree distribution with finite mean (§4 assumptions) → any probability sequence q on ℕ; reason: the market's law p⁻_j = Σ_k (k/λ) p_jk is a probability sequence, so the source's statement is the special case q = p⁻
--   - encoding: 'monotonically decreasing' → AntitoneOn (weakly decreasing); reason: f = 1 on an initial interval (p.53: f = 1 for x ∈ [0, x_c]), so the page means weak monotonicity
-- source:
--   Aymanns, Georg, Golub, Exit Spirals in Coupled Networked Markets, SSRN 2881814 (preprint, sha256 12000f11…6c84d2), Lemma 8, p.53 (corrected)

import Mathlib
import Definitions.Def_ExitSpirals_pgf

namespace ExitSpirals

/-- **Lemma 8, corrected: the smallest root `f(s)` of `f = H(1 − s + s f)` is decreasing in `s`,
and continuous unless the offspring law is the point mass at 1.**
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814, Lemma 8, p.53:
"Let f(x) denote the smallest solution f = H(f, x). Then f(x) is continuous, monotonically
decreasing in x for x ∈ [0, 1]", with `H(f, x) = H(1 − x + x f)` (proof of Proposition 4, p.53).

For a probability sequence `q` on `ℕ` with generating function `H`:
1. `s ↦ f(s) = smallestRoot q s` is antitone on `[0, 1]`;
2. if `q_1 < 1`, it is continuous on `[0, 1]`.

**Formalization Note.** "Decreasing" is weak: `f = 1` on `[0, x_c]`. The paper's variable `x` is
`s` here. -/
theorem lemma_8 (q : ℕ → ℝ) (hq0 : ∀ j, 0 ≤ q j) (hq1 : HasSum q 1) :
    AntitoneOn (smallestRoot q) (Set.Icc (0 : ℝ) 1) ∧
      (q 1 < 1 → ContinuousOn (smallestRoot q) (Set.Icc (0 : ℝ) 1)) := by sorry

end ExitSpirals
