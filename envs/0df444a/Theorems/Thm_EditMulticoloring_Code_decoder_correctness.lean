-- Prove2me | Theorems.Thm_EditMulticoloring_Code_decoder_correctness
-- name    : EditMulticoloring.Code.decoder_correctness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T18:50:27.527296+00:00
-- url     : https://prove2.me/theorems/779d69c6-b16e-4997-9517-65a169acbf44
-- title:
--   Lemma 12 — Message recovery and exact rejection
-- statement:
--   Fix $q\ge2,t\ge1$, use the source parameters at a length where $m\ge1$, and choose a valid polynomial-basis representation. Let $C_n$ be Construction 3.1 and let $D_n$ be the complete decoder of §3.2, including suffix membership and inversion, both parsing checks, good-prime and residue checks, and the rank cutoff. For every message $u\in A^k$ and every finite received word $y\in A^*$,
--
--   $$D_n(y)=u\quad\Longleftrightarrow\quad d_E(y,C_n(u))\le t.$$
--
--   Moreover,
--
--   $$D_n(y)=\mathrm{reject}\quad\Longleftrightarrow\quad\forall u\in A^k,\ d_E(y,C_n(u))>t.$$
--
--   Thus the first passing candidate returns the transmitted message, and words outside every codeword ball are rejected. The domain includes empty words and arbitrarily long invalid inputs.
--
--   Differences from the source:
--   - encoding: the finite field of order Q with a chosen binary polynomial-basis representation → bit-mask polynomial arithmetic modulo any monic irreducible polynomial of degree log2 Q; reason: these are the coefficient-vector labels of Appendix D.1; the goal concludes validity and operational realization rather than assuming a free field oracle
--   - encoding: Construction 3.1 is used after n is large enough that m is positive → the decoder lemma is stated at every n satisfying m at least 1; reason: this exposes the construction domain; the main theorem concludes positivity beyond a uniform threshold
--   - encoding: finite words over an alphabet of q symbols and one-based positions → lists of Fin q, finite-coordinate functions for fixed lengths, and zero-based stored operations; reason: order-preserving conversion and the explicit interval formula preserve every source word and positioned edit
--   - encoding: return the recovered message or reject the received word → Option of a word, with some u for message u and none for rejection; reason: this represents the two source outcomes explicitly and preserves recovery and exact rejection on every finite received word
-- source:
--   Huiling Xie, Zitan Chen, Explicit Edit Codes via Multicoloring, STOC 2027 submission #819 (October 2026), Lemma 12, printed p. 12 (PDF p. 13), procedure printed pp. 11–12 (PDF pp. 12–13); pinned repository artifact papers/stoc2027-819/source.pdf, SHA256 00172d5da76bf6bc886b8a1f87450befb76480107f54cb367988a065737eb376.

import Definitions.Def_EditMulticoloring_Code_Construction

namespace EditMulticoloring.Code

theorem decoder_correctness (q t : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t)
    (n : ℕ) (hm : 1 ≤ (parameters q t n).m)
    (p : ℕ) (hp : ValidModulus
      (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1)) p) :
    (∀ (u : FixedWord q (parameters q t n).k) (y : Word q),
      decode t n p y = some (toWord u) ↔ distance y (encode t n p (toWord u)) ≤ t) ∧
    (∀ y : Word q, decode t n p y = none ↔
      ∀ u : FixedWord q (parameters q t n).k, t < distance y (encode t n p (toWord u)))
    := by sorry

end EditMulticoloring.Code
