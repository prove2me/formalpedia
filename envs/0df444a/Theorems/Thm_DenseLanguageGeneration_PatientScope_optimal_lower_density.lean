-- Prove2me | Theorems.Thm_DenseLanguageGeneration_PatientScope_optimal_lower_density
-- name    : DenseLanguageGeneration.PatientScope.optimal_lower_density
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:49:19.314644+00:00
-- url     : https://prove2.me/theorems/d6cadad1-8527-4c08-9427-9cc8dffb8743
-- title:
--   Theorem 3.15 — optimal one-half lower density, including validity
-- statement:
--   For every indexed countable family $\mathcal L=(L_1,L_2,\ldots)$ of infinite positive-integer languages, every target $K=L_{i_\star}$ and every injective full enumeration $a$ of $K$, the operational patient-scope generator $G_{\mathcal L}$ generates $K$ in the limit without repeating a previous announcement, and
--
--   $$
--   \operatorname{ld}(G_{\mathcal L},K,a)
--   =\liminf_{n\to\infty}\frac{\mu_n(D\cap K)}{\mu_n(K)}\ge\frac12.
--   $$
--
--   Here $D$ is computed from first announcements in the actual run, and $\mu_n$ counts the ambient prefix $\{1,\ldots,n\}$. Optimality has the matching worst-case meaning: for every family $\mathcal L$, every target $K=L_{i}$ in it, and every deterministic generator $G$ (which may depend on $\mathcal L$),
--
--   $$
--   \exists a\text{ an injective full enumeration of }K:
--   \quad\operatorname{ld}(G,K,a)\le\frac12.
--   $$
--
--   The family is fixed before the secret target and its run; neither is a generator argument. Quantification over all legal full streams covers adaptive adversaries because the generator is deterministic and causal. Competitors are arbitrary finite-history generators, without an additional freshness or validity restriction. The adversary's witness must enumerate every member of $K$, including integers already output by the generator. Taking the constant family $L_i=\mathbb N_+$ gives the single-language instance.
--
--   This is the full deterministic single-order result with its §2 optimality context. It does not assert that every patient-scope run has density exactly one half. Validity and the density guarantee are conclusions, not input assumptions.
--
--   Differences from the source:
--   - encoding: positive family indices and rounds → family index i means source index i+1; stream index t means round t+1; history at completed time t has t inputs; reason: bijections preserve the countable family and every legal causal run, including the initial time zero
--   - encoding: optimal lower density 1/2, with the universal validity objective and deterministic upper bound stated in section 2 → one conjunction of universal validity and at-least-one-half density for patient-scope, plus, for every family, target and deterministic generator, a legal full enumeration of that target with lower density at most one half; reason: makes the source optimality quantifiers explicit; all legal full enumerations are included and no competing generator is excluded
--   - encoding: real ambient-prefix liminf with a denominator that is eventually nonzero → real Filter.liminf, using zero for ratios at zero denominator; reason: K is infinite, every ratio lies in [0,1], and only finitely many initial prefixes have zero denominator
-- source:
--   Cai, Li, Shen, Wang and Zhang, STOC 2027 submission #335 (October 2026), Theorem 3.15 and proof, printed pp.16–17 (PDF pp.18–19); Definitions 2.1–2.2, printed p.7 (PDF p.9); deterministic sharpness paragraph, printed p.8 (PDF p.10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_DenseLanguageGeneration_PatientScope_density

set_option autoImplicit false
open ActiveLanguageGeneration.Hierarchy

namespace DenseLanguageGeneration.PatientScope

/-- Cai et al., STOC 2027 submission #335 (October 2026), Theorem 3.15,
printed pp.16--17 (PDF pp.18--19), with deterministic sharpness from §2,
printed p.8 (PDF p.10). Validity and the exact half guarantee hold on every legal
run of the operational algorithm. For every family and every target in it, every
deterministic competitor (chosen after the family) faces a legal full enumeration of
that target with lower density at most one half. -/
theorem optimal_lower_density :
    (∀ (L : Family) (i : ℕ) (a : ℕ → ℕ+), IsEnumeration (L i) a →
      Generates (generator L) (L i) a ∧
      (1 / 2 : ℝ) ≤ lowerDensity (generator L) (L i) a) ∧
    (∀ (L : Family) (i : ℕ) (G : Generator ℕ+), ∃ a : ℕ → ℕ+,
      IsEnumeration (L i) a ∧ lowerDensity G (L i) a ≤ (1 / 2 : ℝ)) := by sorry

end DenseLanguageGeneration.PatientScope
