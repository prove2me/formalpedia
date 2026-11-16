-- Prove2me | Theorems.Thm_DenseLanguageGeneration_PatientScope_Supplement_partial_enumeration_lower_density
-- name    : DenseLanguageGeneration.PatientScope.Supplement.partial_enumeration_lower_density
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:05:50.648769+00:00
-- url     : https://prove2.me/theorems/5f712137-26e7-46cb-a96c-9b8e5d146048
-- title:
--   Theorem B.3 — Lower density from partial enumeration
-- statement:
--   Let $\mathcal L$ be a known countably indexed family of infinite languages, let $K=L_i$ be the secret true language, and let $K'\subseteq K$ be infinite. Suppose $K'$ has relative lower density $\alpha$ in $K$:
--
--   $$\liminf_{n\to\infty}\frac{|K'\cap[n]|}{|K\cap[n]|}=\alpha.$$
--
--   For every full injective enumeration $a$ of $K'$, run the published patient-scope generator on the constructed family $\mathcal L'$ of infinite finite intersections in increasing binary-code order. Its ownership set $D$ satisfies
--
--   $$\liminf_{n\to\infty}\frac{|D\cap K\cap[n]|}{|K\cap[n]|}\ge\frac\alpha2.$$
--
--   The language $K'$ need not belong to the family, and $\alpha=0$ is permitted. This companion theorem measures the generator's density in $K$, rather than in the enumerated subset. Lemma B.2 supplies the accompanying validity statement.
--
--   Differences from the source:
--   - encoding: positive family indices and rounds → zero-based Family and stream indices; the response at index t sees inputs 0 through t; reason: adding one identifies the indices, and causal replay also recovers the generator's own past outputs
--   - encoding: positive binary codes with finite intersections discarded → code c stands for c+1, and Nat.nth enumerates all infinite intersections in increasing code order; reason: this preserves the source order and singleton intersections without imposing the expository assumption that every intersection is infinite
--   - encoding: prefix-count ratios and their asymptotic lower limits → real ratios with zero at a zero denominator and Filter.liminf atTop; reason: all numerators are measurable finite counts bounded by the corresponding denominator; an infinite target has eventually positive denominators, so the total convention changes no lower density
-- source:
--   Ziyi Cai, Shuangping Li, Yiheng Shen, Kangning Wang and Peng Zhang, Dense Language Generation Made Simple: Deterministic, Randomized, and Multi-Order Algorithms, STOC 2027 submission #335 (October 2026), Theorem B.3, printed p.41 (PDF p.43); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_DenseLanguageGeneration_PatientScope_Supplement_intersectionClosure

set_option autoImplicit false
open ActiveLanguageGeneration.Hierarchy
open DenseLanguageGeneration.PatientScope
open Filter Topology

namespace DenseLanguageGeneration.PatientScope.Supplement

/-- Cai et al., STOC 2027 submission #335 (October 2026), Theorem B.3,
printed p.41 (PDF p.43). If K′ ⊆ K = L i has lower density α in K, the patient-scope
algorithm on ℒ′ has lower density at least α/2 measured in K (ambient prefixes,
the published `lowerDensity`), on every enumeration of K′. -/
theorem partial_enumeration_lower_density (L : Family) (i : ℕ)
    (K' : ActiveLanguageGeneration.Hierarchy.Language ℕ+) (hK' : K'.val ⊆ (L i).val)
    (α : ℝ) (hα : relativeLowerDensity K'.val (L i) = α)
    (a : ℕ → ℕ+) (ha : IsEnumeration K' a) :
    α / 2 ≤ lowerDensity (generator (intersectionClosure L)) (L i) a := by sorry

end DenseLanguageGeneration.PatientScope.Supplement
