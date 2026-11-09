-- Prove2me | Theorems.Thm_EditMulticoloring_Code_prime_multicoloring
-- name    : EditMulticoloring.Code.prime_multicoloring
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T18:49:42.983729+00:00
-- url     : https://prove2.me/theorems/5eff1f2e-3c7a-48b5-a92e-ab2aa75523f5
-- title:
--   Lemma 9 — Prime multicoloring
-- statement:
--   Let $G$ be a finite simple graph of degree at most $r$, let $q\ge2$ and $B\ge1$, and let $f:V\to\{0,\ldots,2^B-1\}$ be a proper coloring. Define $L=4(r+1)(B+1)$, $J=q^{\lfloor\log_q(L/2)\rfloor}$, and let $p_1=2,p_2,\ldots$ be the increasing primes. An index $i<L$ is good for $v$ if reduction modulo $p_{i+1}$ distinguishes its label from all neighboring labels. With $i_v(j)$ the index of its $(j+1)$-st good prime, set
--
--   $$S(v)=\{(i_v(j),f(v)\bmod p_{i_v(j)+1}):0\le j<J\}.$$
--
--   Every vertex has at least $J$ good indices, every pair lies in the palette, and
--
--   $$|S(v)|=J,\qquad S(u)\cap S(v)=\varnothing\quad(uv\in E).$$
--
--   The conclusion establishes well-defined allocation as well as its size and edge disjointness.
--
--   Differences from the source:
--   - generalization: Eq. (3) calls r the maximum degree → r can be any nonnegative integer upper bound on degrees; reason: the proof uses only the degree inequality, as does the source application with r=r_(2t)(n); choosing the actual maximum recovers every stated source instance
-- source:
--   Huiling Xie, Zitan Chen, Explicit Edit Codes via Multicoloring, STOC 2027 submission #819 (October 2026), Lemma 9, printed p. 8 (PDF p. 9), using Definition 8 and Eqs. (3)–(6), printed pp. 7–8 (PDF pp. 8–9); pinned repository artifact papers/stoc2027-819/source.pdf, SHA256 00172d5da76bf6bc886b8a1f87450befb76480107f54cb367988a065737eb376.

import Definitions.Def_EditMulticoloring_Code_Graph

namespace EditMulticoloring.Code

theorem prime_multicoloring {V : Type} [Fintype V]
    (q : ℕ) (hq : 2 ≤ q) (G : SimpleGraph V) (r B : ℕ)
    (hB : 1 ≤ B) (degree : ∀ v, (neighbors G v).card ≤ r)
    (f : V → ℕ) (range : ∀ v, f v < 2 ^ B)
    (proper : ∀ u v, G.Adj u v → f u ≠ f v) :
    let L := paletteLength r B
    let J := foldCount q L
    (∀ v, J ≤ (goodIndices G f L v).length) ∧
    (∀ v, (assigned G f L J v).card = J ∧ assigned G f L J v ⊆ palette L) ∧
    (∀ u v, G.Adj u v → Disjoint (assigned G f L J u) (assigned G f L J v))
    := by sorry

end EditMulticoloring.Code
