-- Prove2me | Theorems.Thm_ExitSpirals_lemma_9
-- name    : ExitSpirals.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:01:52.889047+00:00
-- url     : https://prove2.me/theorems/f41978f6-f6c4-4c19-b7e2-296d8901e3f7
-- title:
--   Lemma 9 (corrected: in-degree $g$, C1; continuity needs $p^-_1<1$, C4) — $g(s)$ is increasing and continuous
-- statement:
--   Let $p$ be a joint degree distribution and $g(s)=1-G(1-s+s\,f(s))$ its corrected giant-component fraction. Then
--
--   1. $g$ is (weakly) increasing on $[0,1]$;
--   2. if the link-origin in-degree law satisfies $p^-_1<1$, $g$ is continuous on $[0,1]$.
--
--   These are the two properties of $g$ that make $F(s,x)=x\,g_R(x\,g_C(s))$ monotone and continuous.
--
--   Differences from the source:
--   - correction: (9) and Lemma 5: g(f) = 1 − Σ_jk p_jk f^k with H built from p⁺_k = Σ_j (j/λ) p_jk (out-links) → g(s) = 1 − G(1 − s + s f(s)), G(z) = Σ_jk p_jk z^j, f the smallest root of f = H(1 − s + s f) with H built from p⁻_j = Σ_k (k/λ) p_jk (p.46); reason: the printed formula measures who can reach the giant component, but stability needs support from it: with in-degree 2 for all agents and out-degree 0 or 4 with probability ½ (Assumption 4.5 holds), every agent is active at x = 1 by Lemma 2, while the printed g gives ½ − ½f⁴ < ½
--   - correction: continuity on all of [0, 1] → continuity under the exclusion of the point mass at 1 (q_1 < 1, resp. p⁻_1 < 1); reason: for q = δ_1, H(z) = z: f(s) = 1 for s < 1 and f(1) = 0, so f, g and F jump at s = 1 (proved in the verification file)
--   - generalization: under the assumptions of §4 (Assumption 4.5, well-behaved tuples) → any joint degree distribution (Assumption A.1(2) only); reason: the source's laws satisfy IsDegreeDist, so the source's case is a special case
--   - encoding: 'monotonically increasing' → MonotoneOn (weakly increasing); reason: g = 0 for small s (p.55), so the page means weak monotonicity
-- source:
--   Aymanns, Georg, Golub, Exit Spirals in Coupled Networked Markets, SSRN 2881814 (preprint, sha256 12000f11…6c84d2), Lemma 9, p.54 (corrected)

import Mathlib
import Definitions.Def_ExitSpirals_IsDegreeDist
import Definitions.Def_ExitSpirals_giantFrac

namespace ExitSpirals

/-- **Lemma 9, corrected: `g(s)` is increasing in `s`, and continuous unless the link-origin
in-degree law is the point mass at 1.**
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814, Lemma 9, p.54:
"g(f, x) is continuous and monotonically increasing in x for x ∈ [0, 1]."

For a joint degree distribution `p`:
1. `g = giantFrac p` is monotone on `[0, 1]`;
2. if `p⁻_1 < 1` (`edgeOriginIn p 1 < 1`), `g` is continuous on `[0, 1]`.

**Formalization Note.** `g(s) = 1 − G(1 − s + s f(s))`, the corrected `g` of (9). "Increasing"
is weak: `g = 0` for small `s`. -/
theorem lemma_9 (p : ℕ → ℕ → ℝ) (hp : IsDegreeDist p) :
    MonotoneOn (giantFrac p) (Set.Icc (0 : ℝ) 1) ∧
      (edgeOriginIn p 1 < 1 → ContinuousOn (giantFrac p) (Set.Icc (0 : ℝ) 1)) := by sorry

end ExitSpirals
