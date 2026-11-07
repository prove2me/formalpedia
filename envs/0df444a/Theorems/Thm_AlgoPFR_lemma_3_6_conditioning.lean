-- Prove2me | Theorems.Thm_AlgoPFR_lemma_3_6_conditioning
-- name    : AlgoPFR.lemma_3_6_conditioning
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:42:53.476204+00:00
-- url     : https://prove2.me/theorems/442bed8f-79ac-4b1c-8592-799d8265810c
-- title:
--   Lemma 3.6 — conditioning costs half the mutual information
-- statement:
--   Let $(X,J)$ be jointly distributed, with $X$ taking values in $\mathbb F_2^n$, and let $Y$ be an $\mathbb F_2^n$-valued random variable independent of $(X,J)$. Then
--   $$\mathbb E_{j\sim J}\,d[(X\mid J=j);Y]\le d[X;Y]+\tfrac12 I[X:J].$$
--   If moreover $J$ takes at most $m$ values, then
--   $$\mathbb E_{j\sim J}\,d[(X\mid J=j);Y]\le d[X;Y]+\tfrac12\log m.$$
--
--   This is how the source prices the conditioning on a bucket label in Claim 4.10.
--
--   Differences from the source:
--
--   - encoding: J takes at most m values → the support of J lies in a finite set S with |S| ≤ m; reason: the same condition on a label type that may be infinite
--   - encoding: E_{j∼J} over a jointly distributed label → a sum in [0, ∞] over an arbitrary label type, with I[X : J] = H[X] − H[X | J]; reason: chain rule (3) of the source; the sum has no junk value
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Lemma 3.6, p.15

import Mathlib
import Definitions.Def_AlgoPFR_condLaw

set_option autoImplicit false

open scoped ENNReal Pointwise

namespace AlgoPFR

/-- **Lemma 3.6.** Arunachalam, Dutt, Grewal, Gupte, *Marton's conjecture in polynomial time*, arXiv:2609.20771 (sha256 60e45066…), p.15: if `(X, J)` is jointly distributed and `Y` is independent of it, then
`E_{j∼J} d[(X | J = j); Y] ≤ d[X;Y] + ½ I[X : J]`; if `J` takes at most `m` values, then
`E_{j∼J} d[(X | J = j); Y] ≤ d[X;Y] + ½ log m`.

**Formalization Note.** Independence of `Y` is built into `rd`. The expectation lies in `[0, ∞]` since
the label `J` may have infinite range; both right-hand sides are nonnegative, so `ofReal` loses
nothing. -/
theorem lemma_3_6_conditioning {n : ℕ} {ι : Type} (q : PMF (Vec n × ι)) (Y : PMF (Vec n)) :
    expect (q.map Prod.snd) (fun j => rd (labelFiber q j) Y) ≤
        ENNReal.ofReal (rd (q.map Prod.fst) Y + 1 / 2 * labelInfo q) ∧
      ∀ (S : Finset ι) (m : ℕ), (∀ j ∈ (q.map Prod.snd).support, j ∈ S) → S.card ≤ m →
        expect (q.map Prod.snd) (fun j => rd (labelFiber q j) Y) ≤
          ENNReal.ofReal (rd (q.map Prod.fst) Y + 1 / 2 * Real.logb 2 m) := by sorry

end AlgoPFR
