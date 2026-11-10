-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_flattening_entropy
-- name    : BirthdayEntropy.Soundness.flattening_entropy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:51:45.819687+00:00
-- url     : https://prove2.me/theorems/cc7dcd6d-2b3d-470a-a739-c713d41935ab
-- title:
--   Lemma 4.7 — Entropy of the random flattening
-- statement:
--   Fix $d\ge1,\varepsilon>0$. There are uniform constants $C>0$ and $D_1,D_2\ge0$, depending only on these source parameters. For every source in the NO class, every $2\le\ell<\min\{\beta,1/2\}n$, every $K$-vertex selection $H$, and every natural $r$ with a nonempty accepted event, let $Q$ be the actual uniform law on accepted tuples, let $F$ be their signed flattening, put $x=\ell/n$, $A_0=\log(e/x)$, and $L_r=\log(1/p_r)$. Then both
--   $$H_Q(F)\le5I_Q(X_L;X_R)+CA_0\mathbb E_QR(F)+D_1\log(n+1)$$
--   and
--   $$H_Q(F)\le5L_r+CA_0\mathbb E_QR(F)+D_2\log n.$$
--   The same $C$ works in both inequalities. Here the positive acceptance assumption is only for defining $Q$ and the finite real $L_r$; it does not appear in the final soundness theorem. This statement measures the entropy of the actual moving flattening.
--
--   Differences from the source:
--   - encoding: variables [n] and indexed constraints with arbitrary ternary Boolean predicates → Fin n, Fin m and the published RandOrderCSP.CSP 3 Bool with injective scope rows; reason: reindexing and ordering each three-element scope changes no instance or predicate; repeated scopes remain distinct indices
--   - encoding: a source-dependent beta>0 satisfying 2d beta<gamma/2 → beta=min(1/4,epsilon/(48d)), with gamma=epsilon/3; reason: nonisolation gives at least epsilon n/3 violated constraints; this choice is positive and satisfies the required strict inequality
--   - generalization: standing repetition choice (4) and quantitative lower scale threshold → every natural r, including zero, without the lower scale threshold, at 2<=ell<min(beta,1/2)n; reason: the fixed-cell and flattening-entropy arguments use neither the repetition choice nor the lower scale threshold; every source-admitted scale is included by choosing x0<min(beta,1/2)
--   - encoding: two uniform O(logarithm) terms and conditioning on positive acceptance → existential nonnegative D1,D2 and a nonempty accepted set; reason: finite uniform sampling makes event nonemptiness equivalent to positive probability; each coefficient is uniform before n,ell,H,r
-- source:
--   Alexandru Popa, Entropy-Weighted Soundness for Multi-Answer Birthday Graphs, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, Lemma 4.7, PDF pp12 / printed pp11

import Mathlib
import Definitions.Def_BirthdayEntropy_Soundness_Biclique

noncomputable section
open scoped Classical

namespace BirthdayEntropy.Soundness

/-- Lemma 4.7 (13),(14), PDF p12 / printed p11. The logarithmic
error coefficients are uniform and nonnegative. The fixed source beta is
used. Any r is allowed; the entropy proof does not use (4) or the lower scale. -/
theorem flattening_entropy (d ε : ℝ) (hd : 1 ≤ d) (hε : 0 < ε) :
    ∃ C D₁ D₂ : ℝ, 0 < C ∧ 0 ≤ D₁ ∧ 0 ≤ D₂ ∧
      ∀ (n m : ℕ) (φ : CSP n m), Source φ d → Gap φ ε →
      ∀ (ℓ : ℕ), 2 ≤ ℓ → (ℓ : ℝ) < min (beta d ε) (1/2) * n →
      ∀ (H : Finset (Vertex n ℓ)), H.card = Nat.choose n ℓ →
      ∀ (r : ℕ) (hΩ : (accepted φ H r).Nonempty),
        let Q := uniformOn (accepted φ H r) hΩ
        let E := Q.mean (fun X => energy ℓ (beta d ε) (flatten X))
        (Q.map flatten).entropy ≤
          5 * mutualInfo Q Prod.fst Prod.snd + C * logScale n ℓ * E +
            D₁ * Real.log ((n : ℝ) + 1) ∧
        (Q.map flatten).entropy ≤
          5 * Real.log (1 / acceptanceProbability φ H r) + C * logScale n ℓ * E +
            D₂ * Real.log (n : ℝ) := by sorry

end BirthdayEntropy.Soundness
