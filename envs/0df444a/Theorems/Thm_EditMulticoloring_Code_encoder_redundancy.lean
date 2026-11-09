-- Prove2me | Theorems.Thm_EditMulticoloring_Code_encoder_redundancy
-- name    : EditMulticoloring.Code.encoder_redundancy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T18:50:14.029629+00:00
-- url     : https://prove2.me/theorems/73cb63a3-8769-415d-a9f7-3ab7d3149ed6
-- title:
--   Lemma 11 — Injectivity, exact capacity and redundancy
-- statement:
--   Fix $q\ge2$ and $t\ge1$, and use precisely the public parameters and encoder $C_n$ of Construction 3.1, including the first separating point, the first $J$ good primes, fixed-width serialization and the greedy short code. For all sufficiently large $n$, the prefix has positive length and $m+\rho=n$. For every valid polynomial-basis representation, $C_n:A^k\to A^n$ is injective, its image $\mathcal C_n$ satisfies
--
--   $$|\mathcal C_n|=Jq^m=q^k,$$
--
--   and its redundancy satisfies the two-sided estimate
--
--   $$\left|(n-k)-2t\log_q n\right|\le C\log\log n.$$
--
--   Here $C>0$ and the threshold depend only on $q,t$, not on the input, block length or field representation. This states the full redundancy equality of the construction, including both cardinality identities.
--
--   Differences from the source:
--   - encoding: the finite field of order Q with a chosen binary polynomial-basis representation → bit-mask polynomial arithmetic modulo any monic irreducible polynomial of degree log2 Q; reason: these are the coefficient-vector labels of Appendix D.1; the goal concludes validity and operational realization rather than assuming a free field oracle
--   - encoding: n-k = 2t log_q n + O_(q,t)(log log n) → an absolute-value error bound with a positive constant and threshold before n and the field representation; reason: this expands the two-sided asymptotic equality with uniform q,t-dependent constants; n at least 3 makes log log n positive
--   - encoding: finite words over an alphabet of q symbols and one-based positions → lists of Fin q, finite-coordinate functions for fixed lengths, and zero-based stored operations; reason: order-preserving conversion and the explicit interval formula preserve every source word and positioned edit
-- source:
--   Huiling Xie, Zitan Chen, Explicit Edit Codes via Multicoloring, STOC 2027 submission #819 (October 2026), Lemma 11, printed pp. 10–11 (PDF pp. 11–12), with Eqs. (7)–(13); pinned repository artifact papers/stoc2027-819/source.pdf, SHA256 00172d5da76bf6bc886b8a1f87450befb76480107f54cb367988a065737eb376.

import Definitions.Def_EditMulticoloring_Code_Construction

namespace EditMulticoloring.Code

theorem encoder_redundancy (q t : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 3 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      let P := parameters q t n
      1 ≤ P.m ∧ P.m + P.ρ = n ∧
      ∀ p : ℕ, ValidModulus (ceilLog 2 (P.r * P.K + 1)) p →
        (∀ u : FixedWord q P.k, (encode t n p (toWord u)).length = n) ∧
        Function.Injective (fun u : FixedWord q P.k => encode t n p (toWord u)) ∧
        (code q t n p).card = P.J * q ^ P.m ∧
        (code q t n p).card = q ^ P.k ∧
        |((n : ℝ) - (P.k : ℝ)) - (2 * t : ℕ) * logBase q n| ≤
          C * Real.log (Real.log (n : ℝ))
    := by sorry

end EditMulticoloring.Code
