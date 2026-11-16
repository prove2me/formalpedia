-- Prove2me | Theorems.Thm_DenseLanguageGeneration_PatientScope_Supplement_partial_validity
-- name    : DenseLanguageGeneration.PatientScope.Supplement.partial_validity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:05:16.324039+00:00
-- url     : https://prove2.me/theorems/691aa154-f82a-4cd0-9d14-d5f29c2a716f
-- title:
--   Lemma B.2 — Validity under partial enumeration
-- statement:
--   Let $\mathcal L$ be a known countably indexed family of infinite languages and let $K=L_i$ be its secret target. Let $K'\subseteq K$ be any infinite subset, which need not belong to $\mathcal L$, and let $a$ enumerate $K'$ injectively and completely. Form $\mathcal L'$ by retaining the infinite finite intersections in increasing binary-code order. Then the published patient-scope generator applied to $\mathcal L'$ generates $K$ in the limit:
--
--   $$\exists N\ \forall t\ge N,\quad G_{\mathcal L'}(a_0,\ldots,a_t)\in K\setminus\bigl(\{a_0,\ldots,a_t\}\cup\{G_{\mathcal L'}(a_0,\ldots,a_s):s<t\}\bigr).$$
--
--   This supporting lemma is used in the proof of Theorem B.3. Eventual validity and novelty are relative to the true language $K$, while only $K'$ is enumerated; finite intersections are discarded without assuming they are infinite.
--
--   Differences from the source:
--   - encoding: positive family indices and rounds → zero-based Family and stream indices; the response at index t sees inputs 0 through t; reason: adding one identifies the indices, and causal replay also recovers the generator's own past outputs
--   - encoding: positive binary codes with finite intersections discarded → code c stands for c+1, and Nat.nth enumerates all infinite intersections in increasing code order; reason: this preserves the source order and singleton intersections without imposing the expository assumption that every intersection is infinite
-- source:
--   Ziyi Cai, Shuangping Li, Yiheng Shen, Kangning Wang and Peng Zhang, Dense Language Generation Made Simple: Deterministic, Randomized, and Multi-Order Algorithms, STOC 2027 submission #335 (October 2026), Lemma B.2, printed p.40 (PDF p.42); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_DenseLanguageGeneration_PatientScope_Supplement_intersectionClosure

set_option autoImplicit false
open ActiveLanguageGeneration.Hierarchy
open DenseLanguageGeneration.PatientScope
open Filter Topology

namespace DenseLanguageGeneration.PatientScope.Supplement

/-- Cai et al., STOC 2027 submission #335 (October 2026), Lemma B.2,
printed p.40 (PDF p.42); proof printed pp.40–41 (PDF pp.42–43).
Partial enumeration: the adversary enumerates an infinite K′ ⊆ K = L i (K′ need not
be in the family). Generation in the limit is relative to K, not K′. -/
theorem partial_validity (L : Family) (i : ℕ)
    (K' : ActiveLanguageGeneration.Hierarchy.Language ℕ+) (hK' : K'.val ⊆ (L i).val)
    (a : ℕ → ℕ+) (ha : IsEnumeration K' a) :
    Generates (generator (intersectionClosure L)) (L i) a := by sorry

end DenseLanguageGeneration.PatientScope.Supplement
