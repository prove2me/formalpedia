-- Prove2me | Theorems.Thm_DenseLanguageGeneration_PatientScope_eventually_critical
-- name    : DenseLanguageGeneration.PatientScope.eventually_critical
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:47:24.345926+00:00
-- url     : https://prove2.me/theorems/8da9c5bd-2459-4579-9a5a-51a407e4dc9a
-- title:
--   Lemma 3.4 — eventual criticality
-- statement:
--   Let $\mathcal L=(L_1,L_2,\ldots)$ be any indexed family of infinite positive-integer languages, fix a target index $i_\star$, and let $a$ enumerate $K=L_{i_\star}$ injectively and completely. Then
--
--   $$
--   \exists T<\infty\ \forall t\ge T:\quad K\text{ is critical after the first }t\text{ inputs}.
--   $$
--
--   The time may depend on the family, chosen target index and enumeration. Criticality uses containment in earlier critical languages. No target minimality, scope inclusion or eventual correctness is assumed. This stabilization result supplies the criticality input for validity of patient-scope.
--
--   Differences from the source:
--   - encoding: positive family indices and rounds → family index i means source index i+1; stream index t means round t+1; history at completed time t has t inputs; reason: bijections preserve the countable family and every legal causal run, including the initial time zero
-- source:
--   Cai, Li, Shen, Wang and Zhang, STOC 2027 submission #335 (October 2026), Lemma 3.4, printed p.10 (PDF p.12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_DenseLanguageGeneration_PatientScope_criticalChain

set_option autoImplicit false
open ActiveLanguageGeneration.Hierarchy

namespace DenseLanguageGeneration.PatientScope

/-- Cai et al., STOC 2027 submission #335 (October 2026), Lemma 3.4,
printed p.10 (PDF p.12). No scope or algorithm-success hypothesis. -/
theorem eventually_critical (L : Family) (i : ℕ) (a : ℕ → ℕ+)
    (ha : IsEnumeration (L i) a) :
    ∃ T : ℕ, ∀ t ≥ T, Critical L (history a t) i := by sorry

end DenseLanguageGeneration.PatientScope
