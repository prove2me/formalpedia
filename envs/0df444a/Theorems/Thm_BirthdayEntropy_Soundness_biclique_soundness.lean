-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_biclique_soundness
-- name    : BirthdayEntropy.Soundness.biclique_soundness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:51:38.981702+00:00
-- url     : https://prove2.me/theorems/a61eeefc-068e-4add-bb61-ebc1cfc7b1e8
-- title:
--   Theorem 4.9 — Entropy-weighted biclique soundness
-- statement:
--   For each real $d\ge1,\varepsilon>0$ there are $C_0,C_*,c>0$ and $0<x_0<\min\{\beta,1/2\}$ depending only on $d,\varepsilon$. For every source in the NO class and every $\ell$ with $2\le\ell\le x_0n$ and $\ell\log(en/\ell)\ge C_0\log(n+1)$, every $K$-vertex selection $H$ satisfies, at $x=\ell/n$, $A_0=\log(e/x)$ and $r=\lceil C_*A_0/x\rceil$,
--   $$p_r\le\exp(-cnxA_0).$$
--   For $p_r>0$ this is exactly $L_r\ge cnxA_0$. At zero acceptance it states the correct extended-information case without totalizing a real logarithm at zero. This is the accepted-biclique soundness milestone.
--
--   Differences from the source:
--   - encoding: variables [n] and indexed constraints with arbitrary ternary Boolean predicates → Fin n, Fin m and the published RandOrderCSP.CSP 3 Bool with injective scope rows; reason: reindexing and ordering each three-element scope changes no instance or predicate; repeated scopes remain distinct indices
--   - encoding: a source-dependent beta>0 satisfying 2d beta<gamma/2 → beta=min(1/4,epsilon/(48d)), with gamma=epsilon/3; reason: nonisolation gives at least epsilon n/3 violated constraints; this choice is positive and satisfies the required strict inequality
--   - encoding: Lr>=cnxA0, with Lr=+infinity when pr=0 → pr<=exp(-cnxA0), using the actual accepted count; reason: equivalent at positive acceptance and includes zero acceptance; existential C0,x0 expose the section standing thresholds
-- source:
--   Alexandru Popa, Entropy-Weighted Soundness for Multi-Answer Birthday Graphs, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, Theorem 4.9, PDF pp14 / printed pp13

import Mathlib
import Definitions.Def_BirthdayEntropy_Soundness_Biclique

noncomputable section
open scoped Classical

namespace BirthdayEntropy.Soundness

/-- Theorem 4.9 (18), PDF p14 / printed p13. Equivalent probability
form also represents zero acceptance, where the source information is +infinity. -/
theorem biclique_soundness (d ε : ℝ) (hd : 1 ≤ d) (hε : 0 < ε) :
    ∃ C₀ x₀ Cstar c : ℝ, 0 < C₀ ∧ 0 < x₀ ∧ x₀ < min (beta d ε) (1/2) ∧
      0 < Cstar ∧ 0 < c ∧
      ∀ (n m : ℕ) (φ : CSP n m), Source φ d → Gap φ ε →
      ∀ (ℓ : ℕ), Admitted n ℓ C₀ x₀ →
      ∀ (H : Finset (Vertex n ℓ)), H.card = Nat.choose n ℓ →
        acceptanceProbability φ H (repetition n ℓ Cstar) ≤
          Real.exp (-c * n * ratio n ℓ * logScale n ℓ) := by sorry

end BirthdayEntropy.Soundness
