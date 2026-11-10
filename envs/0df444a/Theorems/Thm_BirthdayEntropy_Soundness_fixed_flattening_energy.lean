-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_fixed_flattening_energy
-- name    : BirthdayEntropy.Soundness.fixed_flattening_energy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:51:31.858861+00:00
-- url     : https://prove2.me/theorems/6a0b1787-e244-4f8c-bb35-dd38bb9af751
-- title:
--   Lemma 4.5 — Quantitative fixed-flattening energy bound
-- statement:
--   Fix real $d\ge1$ and $\varepsilon>0$, and use the indexed Boolean ternary source class and NO promise described above. There is $c_0>0$, depending only on $d,\varepsilon$, such that for every such source, every $2\le\ell<\min\{\beta,1/2\}n$, every selected set $H$ of $K=\binom n\ell$ distinct vertices, every natural $r$, and every cross-consistent signed flattening $(A,B)$,
--   $$|K_{r,r}(A,B)\cap H^{2r}|\le K^{2r}\exp(-c_0rxR(A,B)).$$
--   The cell is the actual accepted fiber, including empty cells; $x=\ell/n$ and $R$ is equation (5). The constant precedes all instances, selections, repetition counts and cells. This statement supplies the quantitative cost of fixing a flattening.
--
--   Differences from the source:
--   - encoding: variables [n] and indexed constraints with arbitrary ternary Boolean predicates → Fin n, Fin m and the published RandOrderCSP.CSP 3 Bool with injective scope rows; reason: reindexing and ordering each three-element scope changes no instance or predicate; repeated scopes remain distinct indices
--   - encoding: a source-dependent beta>0 satisfying 2d beta<gamma/2 → beta=min(1/4,epsilon/(48d)), with gamma=epsilon/3; reason: nonisolation gives at least epsilon n/3 violated constraints; this choice is positive and satisfies the required strict inequality
--   - generalization: standing repetition choice (4) and quantitative lower scale threshold → every natural r, including zero, without the lower scale threshold, at 2<=ell<min(beta,1/2)n; reason: the fixed-cell and flattening-entropy arguments use neither the repetition choice nor the lower scale threshold; every source-admitted scale is included by choosing x0<min(beta,1/2)
-- source:
--   Alexandru Popa, Entropy-Weighted Soundness for Multi-Answer Birthday Graphs, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, Lemma 4.5, PDF pp10 / printed pp9

import Mathlib
import Definitions.Def_BirthdayEntropy_Soundness_Biclique

noncomputable section
open scoped Classical

namespace BirthdayEntropy.Soundness

/-- Lemma 4.5 (6), PDF p10 / printed p9. The statement also covers
arbitrary r, without the quantitative lower scale threshold; the proof of (6)
uses neither the choice (4) nor that threshold. -/
theorem fixed_flattening_energy (d ε : ℝ) (hd : 1 ≤ d) (hε : 0 < ε) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (n m : ℕ) (φ : CSP n m), Source φ d → Gap φ ε →
      ∀ (ℓ : ℕ), 2 ≤ ℓ → (ℓ : ℝ) < min (beta d ε) (1/2) * n →
      ∀ (H : Finset (Vertex n ℓ)), H.card = Nat.choose n ℓ →
      ∀ (r : ℕ) (F : Flattening n), CrossConsistent F →
        ((acceptedCell φ H r F).card : ℝ) ≤ (Nat.choose n ℓ : ℝ)^(2*r) *
          Real.exp (-c₀ * r * ratio n ℓ * energy ℓ (beta d ε) F) := by sorry

end BirthdayEntropy.Soundness
