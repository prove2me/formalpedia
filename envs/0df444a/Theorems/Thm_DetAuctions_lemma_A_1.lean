-- Prove2me | Theorems.Thm_DetAuctions_lemma_A_1
-- name    : DetAuctions.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:56.370898+00:00
-- url     : https://prove2.me/theorems/8e7a0a6a-2432-4f68-842d-d6319f12a34f
-- title:
--   Lemma A.1 — Lipschitz continuity of $\max_a\sum_i\mathsf{SREV}(g_{a,i}(\cdot))$ under a monotone coupling
-- statement:
--   Let $Y,Y'$ be random vectors in $\mathbb R_+^m$, defined on one probability space, with $Y'\le Y$ and $\|Y-Y'\|_\infty\le\delta$ almost surely. Let $A$ be a finite nonempty index set and, for each $a\in A$, let $g_{a,1},\dots,g_{a,n_a}:\mathbb R_+^m\to\mathbb R_+$ be coordinatewise nondecreasing and $L_{a,i}$-Lipschitz for the maximum norm. For
--   $$R(Z)=\max_{a\in A}\sum_{i=1}^{n_a}\mathsf{SREV}\big(g_{a,i}(Z)\big)$$
--   it holds that
--   $$0\le R(Y)-R(Y')\le\delta L,\qquad L=\max_{a\in A}\sum_{i=1}^{n_a}L_{a,i}.$$
--
--   With $Y=X$, $Y'=X^{(K)}$ and $\delta=1/K$ it gives the bounds (6) of Proposition 2.2 for $\mathsf{SREV}$, $\mathsf{BREV}$ and their maximum.
--
--   **Formalization Note** The model is the published `MultiItemRev.Decomp`: values in $\mathbb R_+^m$ (`ι → ℝ≥0`), mechanisms $(a,p)$ with $a\in[0,1]^m$, (DSIC) and (IR) on all of $\mathbb R_+^m$ and a measurable payment; $\mathsf{REV}$ is the supremum of $\mathbb E[p(X)]$ over all of them (lotteries included), in $[0,\infty]$. Independent items are the product of probability laws $F_j$ on $[0,\infty)$. $\mathsf{SREV}$ of a one-dimensional variable is its single-item revenue. The conclusion is stated in $[0,\infty]$ as $R(Y')\le R(Y)\le R(Y')+\delta L$.
--
--   Differences from the source:
--   - reading: E[p(X)] over truthful mechanisms (a, p) → payment p measurable (MultiItemRev.Decomp.IsAdmissible); reason: the expectation E[p(X)] presupposes a measurable payment
--   - encoding: REV_V(X) over a value space V ⊆ ℝ₊^m → V = ℝ₊^m (mechanisms on all of ι → ℝ≥0); reason: REV_V(X) = REV_supp(X)(X) for all supp(X) ⊆ V ⊆ ℝ₊^m (p.8)
--   - encoding: random variables Y, Y′ in ℝ₊^m → measurable maps Y Y' : Ω → ι → ℝ≥0 on a probability space (Ω, P); reason: the standard meaning; no independence between Y and Y′ is assumed, as on the page
--   - encoding: 0 ≤ R(Y) − R(Y′) ≤ δL → R(Y') ≤ R(Y) ∧ R(Y) ≤ R(Y') + δL in ℝ≥0∞; reason: equivalent when R(Y′) is finite and meaningful when it is not
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], Lemma A.1, p.29 (pdf p.31)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory MultiItemRev.Decomp
open scoped NNReal ENNReal

namespace DetAuctions

/-- **Lemma A.1**: let `Y' ≤ Y` with `‖Y − Y'‖∞ ≤ δ` almost surely, and for each `a` in a finite
index set `A` let `g_{a,1}, …, g_{a,n_a} : ℝ₊^m → ℝ₊` be nondecreasing and `L_{a,i}`-Lipschitz for
the maximum norm. For `R(Z) := max_{a∈A} Σᵢ SREV(g_{a,i}(Z))` it holds that
`0 ≤ R(Y) − R(Y') ≤ δL` with `L := max_{a∈A} Σᵢ L_{a,i}`.

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), Lemma A.1, p.29.

**Formalization Note** `Y`, `Y'` are random vectors on one probability space `(Ω, P)` (a
coupling; they are not assumed independent). The distance on `ι → ℝ≥0` is Mathlib's sup
distance, so `dist (Y ω) (Y' ω)` is `‖Y(ω) − Y'(ω)‖∞` and `LipschitzWith` is Lipschitz for the
maximum norm; `L_{a,i} > 0` as in the paper's definition of `L`-Lipschitz (p.7). The SREV of a
one-dimensional variable is its one-item revenue `Rev1` of its law. `A` is nonempty, as
"max over A" requires; the maxima are suprema over the finite `A`. The conclusion
`0 ≤ R(Y) − R(Y') ≤ δL` is stated in `ℝ≥0∞` as `R(Y') ≤ R(Y) ∧ R(Y) ≤ R(Y') + δL`. -/
theorem lemma_A_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type*} [Fintype ι] (Y Y' : Ω → ι → ℝ≥0) (hY : Measurable Y) (hY' : Measurable Y')
    (δ : ℝ≥0) (hle : ∀ᵐ ω ∂P, Y' ω ≤ Y ω) (hdist : ∀ᵐ ω ∂P, dist (Y ω) (Y' ω) ≤ δ)
    {A : Type*} [Fintype A] [Nonempty A] (n : A → ℕ)
    (g : (a : A) → Fin (n a) → (ι → ℝ≥0) → ℝ≥0) (L : (a : A) → Fin (n a) → ℝ≥0)
    (hL : ∀ a i, 0 < L a i) (hmono : ∀ a i, Monotone (g a i))
    (hlip : ∀ a i, LipschitzWith (L a i) (g a i)) :
    (⨆ a, ∑ i, Rev1 (P.map (fun ω => g a i (Y' ω)))) ≤
        (⨆ a, ∑ i, Rev1 (P.map (fun ω => g a i (Y ω)))) ∧
      (⨆ a, ∑ i, Rev1 (P.map (fun ω => g a i (Y ω)))) ≤
        (⨆ a, ∑ i, Rev1 (P.map (fun ω => g a i (Y' ω)))) +
          (δ : ℝ≥0∞) * ⨆ a, ∑ i, (L a i : ℝ≥0∞) := by sorry

end DetAuctions
