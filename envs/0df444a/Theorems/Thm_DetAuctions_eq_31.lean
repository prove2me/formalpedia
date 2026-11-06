-- Prove2me | Theorems.Thm_DetAuctions_eq_31
-- name    : DetAuctions.eq_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:18.015133+00:00
-- url     : https://prove2.me/theorems/289db276-9fe3-41ab-bf43-bf53a59e7e32
-- title:
--   Eq. (31) — Jensen item separation of $\int\phi(\sum_j\bar F_j^{c_j})$
-- statement:
--   Let $\bar F_1,\dots,\bar F_m$ be the tails of nonnegative random variables (the item values), $c_j\ge0$ caps, and $\pi_1,\dots,\pi_m>0$ weights with $\sum_j\pi_j=1$. With $\phi(x)=x-1+e^{-x}$,
--   $$\int_0^\infty\phi\Big(\sum_{j=1}^m\bar F_j^{c_j}(t)\Big)dt\le\int_0^\infty\sum_{j=1}^m\pi_j\,\phi\Big(\frac{\bar F_j^{c_j}(t)}{\pi_j}\Big)dt=\sum_{j=1}^m\pi_j\int_{c_j}^\infty\phi\Big(\frac{\bar F_j(u)}{\pi_j}\Big)du .$$
--
--   The inequality is Jensen's inequality for the convex $\phi$; the equality is the substitution $u=c_j+t$. It separates the items so that each can be controlled by its own cap.
--
--   **Formalization Note** Only the marginal laws enter, as probability laws on $[0,\infty)$. All integrands are nonnegative; the integrals are in $[0,\infty]$. The weights are written $w_j$.
--
--   Differences from the source:
--   - encoding: tails of independent random variables X_j → a family of probability laws ν j on ℝ≥0; reason: the statement involves only the marginal tails, and every family of marginals is realized by independent variables
--   - encoding: ∫ over (0, ∞) (or (c_j, ∞)) of a nonnegative integrand → lower integral of ENNReal.ofReal of the integrand over Set.Ioi, in ℝ≥0∞; reason: the integrands are nonnegative, so ofReal loses nothing and the value +∞ is kept
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], proof of Proposition 4.6, Eq. (31), p.19 (pdf p.21)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model
import Definitions.Def_DetAuctions_tail
import Definitions.Def_DetAuctions_phi

open MeasureTheory MultiItemRev.Decomp
open scoped NNReal ENNReal

namespace DetAuctions

/-- **Eq. (31), Jensen item separation**: for caps `cⱼ ≥ 0` and any weights `πⱼ > 0` with
`Σⱼ πⱼ = 1`,
`∫₀^∞ φ(Σⱼ F̄ⱼ^{cⱼ}(t)) dt ≤ ∫₀^∞ Σⱼ πⱼ φ(F̄ⱼ^{cⱼ}(t)/πⱼ) dt = Σⱼ πⱼ ∫_{cⱼ}^∞ φ(F̄ⱼ(u)/πⱼ) du`.

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), proof of Proposition 4.6, Eq. (31), p.19.

**Formalization Note** The statement concerns only the marginal laws `ν j` (probability laws on
`ℝ≥0`; in the paper they are the laws of independent items). The weights are `w j`. Every
integrand is nonnegative (`φ ≥ 0` on `[0, ∞)`), so the integrals are lower integrals of
`ENNReal.ofReal` over `(0, ∞)` and `(cⱼ, ∞)`, in `ℝ≥0∞` (they may be `+∞`). -/
theorem eq_31 {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ≥0)
    [∀ j, IsProbabilityMeasure (ν j)] (c : ι → ℝ≥0) (w : ι → ℝ) (hw : ∀ j, 0 < w j)
    (hsum : ∑ j, w j = 1) :
    (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (phi (∑ j, (tail (ν j) ((c j : ℝ) + t)).toReal)) ≤
      ∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (∑ j, w j * phi ((tail (ν j) ((c j : ℝ) + t)).toReal / w j))) ∧
    (∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (∑ j, w j * phi ((tail (ν j) ((c j : ℝ) + t)).toReal / w j)) =
      ∑ j, ENNReal.ofReal (w j) *
        ∫⁻ u in Set.Ioi (c j : ℝ), ENNReal.ofReal (phi ((tail (ν j) u).toReal / w j))) := by sorry

end DetAuctions
