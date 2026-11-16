-- Prove2me | Theorems.Thm_DenseLanguageGeneration_PatientScope_Supplement_randomized_upper_bound
-- name    : DenseLanguageGeneration.PatientScope.Supplement.randomized_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:02:50.849512+00:00
-- url     : https://prove2.me/theorems/58b1117d-8364-4c7d-ba3e-dd8424c133db
-- title:
--   Theorem 4.4 — Randomized upper bound
-- statement:
--   Consider the single-language game whose known target is $K=\mathbb Z_{>0}$. For every randomized causal generator $R$ on any probability space, there is one fixed full injective enumeration $a$ of $\mathbb Z_{>0}$ such that
--
--   $$\liminf_{n\to\infty}\frac{\mathbb E_\omega[|D_\omega\cap[n]|]}{n}\le1-e^{-1}.$$
--
--   The enumeration may depend on the generator's law, but cannot depend on its realized random seed. This is the hard instance specified in §4.3 and shows that no randomized generator can guarantee strictly larger density against every non-adaptive adversary. The generator is not assumed valid or successful.
--
--   Differences from the source:
--   - encoding: positive rounds → zero-based stream indices; the response at index t sees inputs 0 through t; reason: adding one identifies the indices, and causal replay also recovers the generator's own past outputs
--   - encoding: a randomized algorithm against a non-adaptive adversary → a probability space with measurable random history responses and an enumeration fixed outside the expectation; reason: presampling the private randomness represents every causal randomized strategy; countable discrete outputs require exactly measurable singleton fibres
--   - encoding: the hard instance ℒ = {ℤ+} in §4.3 → the universal infinite language as a subtype of Set.univ; reason: the known family is constant and therefore supplies no extra information; the generator is quantified universally
--   - encoding: prefix-count ratios and their asymptotic lower limits → real ratios with zero at a zero denominator and Filter.liminf atTop; reason: all numerators are measurable finite counts bounded by the corresponding denominator; an infinite target has eventually positive denominators, so the total convention changes no lower density
-- source:
--   Ziyi Cai, Shuangping Li, Yiheng Shen, Kangning Wang and Peng Zhang, Dense Language Generation Made Simple: Deterministic, Randomized, and Multi-Order Algorithms, STOC 2027 submission #335 (October 2026), Theorem 4.4, printed p.19 (PDF p.21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_DenseLanguageGeneration_PatientScope_Supplement_randomized

set_option autoImplicit false
open ActiveLanguageGeneration.Hierarchy
open DenseLanguageGeneration.PatientScope
open Filter Topology

namespace DenseLanguageGeneration.PatientScope.Supplement

/-- Cai et al., STOC 2027 submission #335 (October 2026), Theorem 4.4,
printed p.19 (PDF p.21); proof in §4.3, printed pp.25–26 (PDF pp.27–28), on the
single-language game ℒ = {ℤ+}. For every randomized algorithm there is ONE fixed
enumeration of ℤ+ (chosen from the algorithm, not from its realized sample) on
which its lower density is at most 1 − 1/e. -/
theorem randomized_upper_bound (R : RandomizedGenerator) :
    ∃ a : ℕ → ℕ+,
      IsEnumeration (⟨Set.univ, Set.infinite_univ⟩ : ActiveLanguageGeneration.Hierarchy.Language ℕ+) a ∧
      randomizedLowerDensity R ⟨Set.univ, Set.infinite_univ⟩ a ≤ 1 - Real.exp (-1) := by sorry

end DenseLanguageGeneration.PatientScope.Supplement
