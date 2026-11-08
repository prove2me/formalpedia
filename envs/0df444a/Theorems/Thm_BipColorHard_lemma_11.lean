-- Prove2me | Theorems.Thm_BipColorHard_lemma_11
-- name    : BipColorHard.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:36:21.845505+00:00
-- url     : https://prove2.me/theorems/d06039db-8f00-41c8-a4aa-206fa3ad95f8
-- title:
--   Lemma 11 — antiferromagnetism between blocks
-- statement:
--   Let $K$ be the connector of Lemma 10, and consider $K$ or $K_L$ with $L\ge L_0$. There are $b>0$ and $\theta>1$ such that, for every edge $\{v,w\}$ of $F$ and all values $\sigma(v),\sigma(w)\in\{0,1\}$ of the blocks of $v$ and $w$, the two connectors between these blocks, one in each direction, have total weight $b^2$ if $\sigma(v)=\sigma(w)$ and $b^2\theta$ otherwise.
--
--   With $\ell$ copies per direction, every cut edge of $F$ then contributes the factor $\beta=\theta^\ell$.
--
--   Differences from the source:
--   - generalization: $K$ or $K_L$ with the $s$ and $L_0$ of Lemma 10 → every $s$, $u$, $L$ at which the conclusion `ConnCorr` of Lemma 10 holds; reason: the proof uses only that conclusion, and Lemma 10 supplies it on the manuscript's range, so this specializes to the source
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), Lemma 11, p.11 (PDF p.13)

import Definitions.Def_BipColorHard_Connector

set_option autoImplicit false

namespace BipColorHard

/-- **Lemma 11**, p.11 (PDF p.13), manuscript sha256 78a66d1f…. Let `K` be the connector of Lemma 10, and consider `K` or `K_L` with `L ≥ L₀`. There are
`b > 0` and `θ > 1` such that, for every edge `{v, w}` of `F` and all values `σ(v), σ(w) ∈ {0, 1}` of the blocks of `v` and `w`, the two connectors
between these blocks, one in each direction, have total weight `b²` if `σ(v) = σ(w)` and `b²θ` otherwise.

**Formalization Note.** Stated at every `s`, `L`, `u` at which the conclusion `ConnCorr` of Lemma 10 holds, which is everything the manuscript's
proof uses; by Lemma 10 this covers the manuscript's range. The value `1` of a block is `true`. -/
theorem lemma_11 (k s : ℕ) (hk : 1 ≤ k) (A0 B0 : Omega k) (hdisj : Disjoint A0.1 B0.1) :
    (ConnCorr (connK k s A0 B0) A0 B0 → ∃ b θ : ℝ, ConnAntiferro (connK k s A0 B0) A0 B0 b θ) ∧
    ∀ (u : ℝ) (L : ℕ), ConnCorr (connKL k s u L A0 B0) A0 B0 →
      ∃ b θ : ℝ, ConnAntiferro (connKL k s u L A0 B0) A0 B0 b θ := by sorry

end BipColorHard
