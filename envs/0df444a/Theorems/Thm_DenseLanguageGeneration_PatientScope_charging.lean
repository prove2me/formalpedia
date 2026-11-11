-- Prove2me | Theorems.Thm_DenseLanguageGeneration_PatientScope_charging
-- name    : DenseLanguageGeneration.PatientScope.charging
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:49:12.530556+00:00
-- url     : https://prove2.me/theorems/5367aa09-5b5d-4e5c-b0fd-50d32f559265
-- title:
--   Lemma 3.14 — charging previously unannounced switch losses
-- statement:
--   Let $\mathcal L$ be any indexed countable family of infinite positive-integer languages, fix $K=L_{i_\star}$, and let $a$ be any injective full enumeration of $K$. There is one finite settling time $T^\star$, independent of the prefix length, for which every positive integer $n$ satisfies
--
--   $$
--   \bigl|\{x\in K[n]: x\text{ is a previously unannounced switch loss occurring after }T^\star\}\bigr|
--   \le \log_2 n.
--   $$
--
--   A switch loss is an input outside the preceding focus; previously unannounced excludes inputs and responses strictly before that input. The settling time also has target criticality, target inclusion in scope and focus containment at all later completed times. Counts are of distinct integers in a finite prefix.
--
--   The prefix $K[n]$ is the first $n$ target integers in increasing order, exactly the source's relabeled $[n]$. The coefficient is one and the logarithm has base two. No positive ambient density, finite family or algorithm-success assumption is imposed.
--
--   Differences from the source:
--   - encoding: positive family indices and rounds → family index i means source index i+1; stream index t means round t+1; history at completed time t has t inputs; reason: bijections preserve the countable family and every legal causal run, including the initial time zero
--   - encoding: after choosing T* in the preceding validity proof, identify K increasingly with the positive integers and count losses in [n] → there exists one settling time T* for the run; count losses directly in the finite rank prefix K[n] of the arbitrary target; reason: packages the already established time as an existential conclusion and transports the relabeled prefix back to K without ranking invalid early outputs
-- source:
--   Cai, Li, Shen, Wang and Zhang, STOC 2027 submission #335 (October 2026), Lemma 3.14 and proof, printed pp.15–16 (PDF pp.17–18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_DenseLanguageGeneration_PatientScope_density

set_option autoImplicit false
open ActiveLanguageGeneration.Hierarchy

namespace DenseLanguageGeneration.PatientScope

/-- Cai et al., STOC 2027 submission #335 (October 2026), Lemma 3.14,
printed pp.15--16 (PDF pp.17--18). K[n] is a rank prefix of the arbitrary
true language. A single run-dependent T* works for every positive n. -/
theorem charging (L : Family) (i : ℕ) (a : ℕ → ℕ+)
    (ha : IsEnumeration (L i) a) :
    ∃ T : ℕ, SettledFrom L i a T ∧ ∀ n : ℕ, 0 < n →
      (lossCount L i a T n : ℝ) ≤ Real.logb 2 (n : ℝ) := by sorry

end DenseLanguageGeneration.PatientScope
