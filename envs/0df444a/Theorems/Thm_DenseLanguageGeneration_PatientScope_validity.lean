-- Prove2me | Theorems.Thm_DenseLanguageGeneration_PatientScope_validity
-- name    : DenseLanguageGeneration.PatientScope.validity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:49:07.092023+00:00
-- url     : https://prove2.me/theorems/46de0ce9-ec78-4e4c-8da2-600a1d234aa8
-- title:
--   Lemma 3.12 — validity and the settling time from its proof
-- statement:
--   Let $\mathcal L$ be any indexed countable family of infinite positive-integer languages, $K=L_{i_\star}$ any target, and $a$ any injective full enumeration of $K$. Run the operational patient-scope generator $G_{\mathcal L}$. There is a finite run-dependent threshold after which every response belongs to $K$ and differs from all inputs through that response and from every earlier response:
--
--   $$
--   \exists t_0\ \forall t\ge t_0:\quad
--   b_t\in K\setminus\bigl(\{a_s:s\le t\}\cup\{b_s:s<t\}\bigr).
--   $$
--
--   Also, as established in the proof, there exists a completed time $T^\star$ such that at every time $t\ge T^\star$, the target is critical and inside the scope, and the focus is a subset of $K$. Both assertions are conclusions, with no successful-run hypothesis.
--
--   This exposes the proof's settling invariant for subsequent counting arguments. Earlier invalid responses still constrain novelty. Thresholds need not be uniform over targets or enumerations.
--
--   Differences from the source:
--   - encoding: positive family indices and rounds → family index i means source index i+1; stream index t means round t+1; history at completed time t has t inputs; reason: bijections preserve the countable family and every legal causal run, including the initial time zero
--   - generalization: the proof supplies target criticality, eventual scope inclusion and the time T* after which foci are subsets of K → eventual NR correctness together with existence of SettledFrom; reason: records the explicit invariant proved on the same page for reuse by the charging lemma; no new hypothesis, and dropping the extra conjunct gives exactly Lemma 3.12
-- source:
--   Cai, Li, Shen, Wang and Zhang, STOC 2027 submission #335 (October 2026), Lemma 3.12 and its proof, printed p.15 (PDF p.17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_DenseLanguageGeneration_PatientScope_density

set_option autoImplicit false
open ActiveLanguageGeneration.Hierarchy

namespace DenseLanguageGeneration.PatientScope

/-- Cai et al., STOC 2027 submission #335 (October 2026), Lemma 3.12
and its concluding proof invariant, printed p.15 (PDF p.17).
T* is furnished by the run, never a hypothesis or a generator argument. -/
theorem validity (L : Family) (i : ℕ) (a : ℕ → ℕ+)
    (ha : IsEnumeration (L i) a) :
    Generates (generator L) (L i) a ∧ ∃ T : ℕ, SettledFrom L i a T := by sorry

end DenseLanguageGeneration.PatientScope
