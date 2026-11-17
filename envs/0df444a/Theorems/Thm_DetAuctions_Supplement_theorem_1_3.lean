-- Prove2me | Theorems.Thm_DetAuctions_Supplement_theorem_1_3
-- name    : DetAuctions.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:43:13.955422+00:00
-- url     : https://prove2.me/theorems/719de90b-10db-4bb4-8471-1c2114b99adf
-- title:
--   Theorem 1.3 — $\mathsf{REV}(F\times F)\le(1+W(1/e))\,\mathsf{SREV}(F\times F)$, and the constant is tight
-- statement:
--   Let $\omega:=W(1/e)\approx0.27846$, where $W$ is the Lambert-W function: for $z\ge0$, $W(z)$ is the unique real $w$ with $we^w=z$. Selling two iid items separately to a single additive buyer guarantees a $(1+\omega)$-approximation to the optimal revenue, and this is tight:
--
--   1. for every distribution $F$ on $[0,\infty)$,
--   $$\mathsf{REV}(F\times F)\le(1+\omega)\,\mathsf{SREV}(F\times F);$$
--   2. for every $\varepsilon>0$ there is a distribution $F$ on $[0,\infty)$ with $0<\mathsf{SREV}(F\times F)<\infty$ and
--   $$\mathsf{REV}(F\times F)\ge(1+\omega-\varepsilon)\,\mathsf{SREV}(F\times F).$$
--
--   This settles the exact worst-case ratio $\mathsf{REV}/\mathsf{SREV}$ for two iid items.
--
--   **Formalization Note** $\omega$ enters as a real number with $\omega\ge0$ and $\omega e^\omega=e^{-1}$; since $w\mapsto we^w$ is strictly increasing on $[0,\infty)$, this is exactly $W(1/e)$ (existence and uniqueness are checked separately). The two items are indexed by `Fin 2`; revenues are in $[0,\infty]$, and for $\varepsilon\ge1+\omega$ the factor $1+\omega-\varepsilon$ is read as $0$.
--
--   Differences from the source:
--   - reading: "there exists a distribution F such that REV(F × F) ≥ (1 + ω − ε) SREV(F × F)" → the witness also has 0 < SREV(F × F) < ∞; reason: as printed, F = δ₀ (both sides 0) satisfies it trivially; the paper's tightness claim is about the ratio REV/SREV, and its witnesses (equal-revenue laws) have finite positive SREV.
--   - encoding: ω := W(1/e) → a real ω with ω ≥ 0 and ω·e^ω = e^{−1}; reason: these conditions determine W(1/e) uniquely (footnote 13), and such an ω exists.
--   - encoding: the factor 1 + ω − ε → ENNReal.ofReal (1 + ω − ε), which is 0 when ε ≥ 1 + ω; reason: revenues live in [0, ∞]; for such ε the source's inequality holds trivially as well.
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], Theorem 1.3, p.6 (pdf p.8); Lambert W per footnote 13, p.22 (pdf p.24)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory MultiItemRev.Decomp
open scoped NNReal ENNReal

namespace DetAuctions.Supplement

/-- **Theorem 1.3** (Tight Approximation Ratio for Two IID Items): with `ω := W(1/e)`, for any
distribution `F`, `REV(F × F) ≤ (1 + ω) SREV(F × F)`; furthermore, for any `ε > 0` there exists a
distribution `F` such that `REV(F × F) ≥ (1 + ω − ε) SREV(F × F)`.

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), Theorem 1.3, p.6 (pdf p.8); Lambert W as in footnote 13, p.22.

**Formalization Note** `ω` is a real parameter with `0 ≤ ω` and `ω · e^ω = e^{-1}`: by
footnote 13, `W(z)` for `z ≥ 0` is the unique real `w` with `w e^w = z`, and `w ↦ w e^w` is
strictly increasing on `[0, ∞)`, so these hypotheses pin `ω = W(1/e) ≈ 0.27846` exactly (such an
`ω` exists, checked in the sanity file). The two items are `Fin 2`; `F × F` is
`Measure.pi (fun _ : Fin 2 => ν)` for an arbitrary probability law `ν` on `[0, ∞)`. In the
tightness part the witness is required to have `0 < SREV < ∞`: otherwise the printed inequality
holds trivially (e.g. `F = δ₀`, where both sides are `0`), and the paper's tightness is a
statement about the ratio `REV/SREV`. For `ε ≥ 1 + ω` the factor `ENNReal.ofReal (1 + ω − ε)` is
`0`. -/
theorem theorem_1_3 (ω : ℝ) (hω0 : 0 ≤ ω) (hω : ω * Real.exp ω = Real.exp (-1)) :
    (∀ (ν : Measure ℝ≥0) [IsProbabilityMeasure ν],
      Rev (Measure.pi (fun _ : Fin 2 => ν)) ≤
        ENNReal.ofReal (1 + ω) * SRev (Measure.pi (fun _ : Fin 2 => ν))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ (ν : Measure ℝ≥0), IsProbabilityMeasure ν ∧
      0 < SRev (Measure.pi (fun _ : Fin 2 => ν)) ∧ SRev (Measure.pi (fun _ : Fin 2 => ν)) < ⊤ ∧
      ENNReal.ofReal (1 + ω - ε) * SRev (Measure.pi (fun _ : Fin 2 => ν)) ≤
        Rev (Measure.pi (fun _ : Fin 2 => ν))) := by sorry

end DetAuctions.Supplement
