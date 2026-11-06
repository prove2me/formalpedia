-- Prove2me | Theorems.Thm_DetAuctions_proposition_3_1
-- name    : DetAuctions.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:31.080203+00:00
-- url     : https://prove2.me/theorems/a18dd833-2737-4ed7-a23c-ae7be1ad1abd
-- title:
--   Proposition 3.1 — master revenue inequality on the grid $I_K$
-- statement:
--   Let $K$ be a positive integer and $X_1,\dots,X_m$ independent random variables with values in the unit grid $I_K$. Then for any caps $c_1,\dots,c_m\in\mathbb R_+$,
--   $$\mathsf{REV}(X)\le\sum_{j=1}^m\max\{r_j,\mathbb E[Z_j]\}+\mathbb E\Big[\sum_{j=1}^m Y_j-\max_{j\in[m]}Y_j\Big],$$
--   where $r_j=\mathsf{REV}(X_j)$, $Z_j=\min\{X_j,c_j\}$ and $Y_j=(X_j-c_j)_+$.
--
--   This weak-duality bound is the paper's main tool: choosing caps with $\mathbb E[Z_j]\le r_j$ turns the first sum into $\mathsf{SREV}(X)$, and the rest of the analysis bounds the residual expectation.
--
--   **Formalization Note** The model is the published `MultiItemRev.Decomp`: values in $\mathbb R_+^m$ (`ι → ℝ≥0`), mechanisms $(a,p)$ with $a\in[0,1]^m$, (DSIC) and (IR) on all of $\mathbb R_+^m$ and a measurable payment; $\mathsf{REV}$ is the supremum of $\mathbb E[p(X)]$ over all of them (lotteries included), in $[0,\infty]$. Independent items are the product of probability laws $F_j$ on $[0,\infty)$. The caps need not be grid points. Both expectations are integrals of nonnegative functions in $[0,\infty]$.
--
--   Differences from the source:
--   - reading: E[p(X)] over truthful mechanisms (a, p) → payment p measurable (MultiItemRev.Decomp.IsAdmissible); reason: the expectation E[p(X)] presupposes a measurable payment
--   - encoding: REV_V(X) over a value space V ⊆ ℝ₊^m → V = ℝ₊^m (mechanisms on all of ι → ℝ≥0); reason: REV_V(X) = REV_supp(X)(X) for all supp(X) ⊆ V ⊆ ℝ₊^m (p.8)
--   - encoding: independent X_j ∼ F_j, real revenues → product law Measure.pi ν of probability laws ν j on ℝ≥0; revenues in ℝ≥0∞; reason: same instances; an unbounded law may have revenue +∞, where the inequalities read in [0, ∞]
--   - encoding: X_j taking values in the unit K-grid I_K, K a positive integer → ν j (gridK K)ᶜ = 0 with 1 ≤ K; reason: almost-sure membership in I_K; the law is unchanged
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], Proposition 3.1 (Master Revenue Inequality), Eq. (8), p.12 (pdf p.14)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model
import Definitions.Def_DetAuctions_gridK
import Definitions.Def_DetAuctions_excessResidual

open MeasureTheory MultiItemRev.Decomp
open scoped NNReal ENNReal

namespace DetAuctions

/-- **Proposition 3.1 (Master Revenue Inequality)**: for independent `X₁, …, X_m` with values in
the unit `K`-grid `I_K` and any caps `c₁, …, c_m ∈ ℝ₊`,
`REV(X) ≤ Σⱼ max{rⱼ, E[Zⱼ]} + E[Σⱼ Yⱼ − maxⱼ Yⱼ]` (8), where `rⱼ = REV(Xⱼ)`,
`Zⱼ = min{Xⱼ, cⱼ}` and `Yⱼ = (Xⱼ − cⱼ)₊`.

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), Proposition 3.1, Eq. (8), p.12.

**Formalization Note** The model is the published `MultiItemRev.Decomp`: item values in `ι → ℝ≥0`, mechanisms
`(q, s)` with allocation in `[0,1]` per item, DSIC and IR on all of `ℝ₊^m` and a measurable
payment; `Rev` is the supremum of the expected payment (an `EReal`, mapped to `ℝ≥0∞`) over all
such mechanisms, `Rev1 ν` the one-item revenue of a law `ν`, `SRev μ = Σⱼ Rev1 (μⱼ)` and
`BRev μ = Rev1 (law of Σⱼ Xⱼ)`. Independent items are the product law `Measure.pi ν` of
probability laws `ν j` on `ℝ≥0`.
"Taking values in `I_K`" is `ν j (gridK K)ᶜ = 0` for a positive integer `K`. The caps are
arbitrary points of `ℝ≥0` (they need not lie on the grid). Both expectations are lower
integrals of nonnegative functions in `ℝ≥0∞`; `excessResidual c x = Σⱼ (xⱼ − cⱼ)₊ − maxⱼ (xⱼ − cⱼ)₊`
(see its definition). -/
theorem proposition_3_1 {ι : Type*} [Fintype ι] (K : ℕ) (hK : 1 ≤ K)
    (ν : ι → Measure ℝ≥0) [∀ j, IsProbabilityMeasure (ν j)]
    (hgrid : ∀ j, ν j (gridK K)ᶜ = 0) (c : ι → ℝ≥0) :
    Rev (Measure.pi ν) ≤
      ∑ j, max (Rev1 (ν j)) (∫⁻ x, ((min x (c j) : ℝ≥0) : ℝ≥0∞) ∂(ν j)) +
        ∫⁻ x, (excessResidual c x : ℝ≥0∞) ∂(Measure.pi ν) := by sorry

end DetAuctions
