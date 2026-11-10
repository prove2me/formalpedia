-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_lemma_14
-- name    : DistancePreserver934.Exact.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:38:43.317795+00:00
-- url     : https://prove2.me/theorems/08bb1822-65f2-42dd-a35b-573eacda35dd
-- title:
--   Lemma 14 — balls around rich vertices grow linearly up to radius $l$
-- statement:
--   Let $H$ be a minimal distance preserver of $(G,R)$, $R$ a demand set, with $\lambda_H(q)\ge l$ for all $q\in R$ and $l\ge1$, and let $V^*$ be a vertex set with loyal core $H_L=(V^*,\Lambda^*_H)$.
--
--   1. If $H_L$ has minimum degree at least $\delta>0$ on $V^*$, then for every rich vertex $u\in V^*$ and every real $a\ge1$,
--   $$|B_H(u,a)|\ge\frac\delta6\min\{a,l\}.\tag{7}$$
--   2. In particular, if $d>0$ and $\deg_{H_L}(x)\ge d/40$ on $V^*$ (the degree part of Equation (6)), then $|B_H(u,a)|\ge\frac{d}{240}\min\{a,l\}$ for every $u\in V^*$ and real $a\ge1$.
--
--   There is no restriction $a\le l$ and $a$ need not be an integer. The bound gives the volume lower bound $u_y=\Omega(dr)$ used in Lemma 17.
--
--   Differences from the source:
--   - encoding: 'in particular, under Equation (6), this is Ω(d min{a, l})' → explicit bound (d/240)·min{a, l} for d > 0; reason: this is (7) at δ = d/40, the constant the source's proof gives
--   - encoding: §5 context |V_H| ≤ n, |E_H| ≤ nd → omitted; reason: n and d occur nowhere else in (7); the omitted conditions are always satisfiable (n = |V|, d = |E_H|), so the statement with and without them is the same
--   - generalization: a dense loyal core satisfying (6), in the standing radius context (5), with the particular consequence under (6) → an arbitrary vertex set V* with its induced private-edge core, using only λ_H(q) ≥ l ≥ 1 and the stated positive degree bound in each clause; no mass bound (6) or radius condition (5); reason: the proof of (7) uses the minimum degree and the private-length bound, not the core mass or the radius parameter; the full source core and radius context specialize to these hypotheses, and δ = d/40 yields the same d/240 consequence
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, Lemma 14, printed p. 15 (PDF p. 16)

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Preservers
import Definitions.Def_DistancePreserver934_Exact_Essential
import Definitions.Def_DistancePreserver934_Exact_LoyalCore

namespace DistancePreserver934.Exact

open Classical

/-- Lemma 14, printed p.15 / PDF p.16.  Let `H` be a minimal distance preserver of `(G, R)` with
`λ_H(q) ≥ l ≥ 1` for all `q ∈ R`, and let `V*` be any vertex set.  If the loyal core on `V*` has
minimum degree at least `δ > 0`, then `|B_H(u, a)| ≥ (δ/6) min{a, l}` for every `u ∈ V*` and every
real `a ≥ 1` (Equation (7)); in particular, under the degree bound of Equation (6) (`δ = d/40`),
`|B_H(u, a)| ≥ (d/240) min{a, l}`. -/
theorem lemma_14 {V : Type} [Fintype V] (G H : SimpleGraph V) (R : Finset (Sym2 V))
    (l : ℝ) (Vs : Finset V)
    (hR : IsDemandSet G R) (hH : IsMinimalPreserver G H R)
    (hlam : ∀ q ∈ R, l ≤ (privLen H R q : ℝ)) (hl : 1 ≤ l) :
    (∀ δ : ℝ, 0 < δ → (∀ x ∈ Vs, δ ≤ (coreDeg H R Vs x : ℝ)) →
      ∀ u ∈ Vs, ∀ a : ℝ, 1 ≤ a → δ / 6 * min a l ≤ ((ball H u a).card : ℝ)) ∧
    (∀ d : ℝ, 0 < d → (∀ x ∈ Vs, d / 40 ≤ (coreDeg H R Vs x : ℝ)) →
      ∀ u ∈ Vs, ∀ a : ℝ, 1 ≤ a → d / 240 * min a l ≤ ((ball H u a).card : ℝ)) := by sorry

end DistancePreserver934.Exact
