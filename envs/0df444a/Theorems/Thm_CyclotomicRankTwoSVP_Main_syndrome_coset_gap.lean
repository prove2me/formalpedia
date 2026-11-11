-- Prove2me | Theorems.Thm_CyclotomicRankTwoSVP_Main_syndrome_coset_gap
-- name    : CyclotomicRankTwoSVP.Main.syndrome_coset_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:57.043443+00:00
-- url     : https://prove2.me/theorems/8ee599b5-d3ba-4fcd-bf2f-53e34bb86147
-- title:
--   Lemma 3.3 — syndrome coset bijection and binary gap
-- statement:
--   Let $q$ be an odd prime, $1\le k\le q/2$, and let $h'\in\mathbb Z$ be arbitrary, including negative values. For every syndrome $u\in\mathbb F_q^k$ with $u_0=h'\pmod q$, there exists an integer vector $z_0$ with syndrome $u$ and coefficient sum $h'$. Evaluation is a bijection
--
--   $$\{z:H_q(k)z=u,\ \sum_a z_a=h'\}\longrightarrow[z_0]+\mathfrak a_{q,k}.$$
--
--   Thus each coset element has exactly one such representative. For every representative $z$ in this fiber, put $H'=h'(q-h')$. If $z$ is binary, its weight is $h'$ and $N([z])=H'$. Otherwise,
--
--   $$N([z])\ge H'+2q.$$
--
--   The statement retains existence, bijectivity, the binary equality and the nonbinary gap. For a negative $h'$ the binary branch is impossible, consistently with the source.
--
--   Differences from the source:
--   - encoding: K = Q(zeta_q), O_K = Z[zeta_q], all complex embeddings → a fixed isomorphic cyclotomic splitting field, the integer adjoin of its primitive root, and all rational algebra embeddings into C; reason: the same prime-conductor field and unnormalized canonical norm, with no additional source hypotheses
--   - encoding: indices [r] = {1,...,r} and field elements F_q → Fin r and ZMod q; beta uses the row index plus one; reason: finite reindexing changes no instance or ordered pair
--   - encoding: coset membership v in [z_0]+a and the unique representative for each v → Set.BijOn evaluation between the actual fixed-syndrome fiber and {v : v-[z_0] in a}, followed by bounds for every fiber representative; reason: the bijection supplies existence and uniqueness; the fiber formulation gives precisely the same norm assertions
-- source:
--   Jiaqi Liu, Yansong Feng, Yanbin Pan, SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules, STOC 2027 submission #1423 (October 2026), printed p. 10 / PDF p. 11, Lemma 3.3

import Mathlib
import Definitions.Def_CyclotomicRankTwoSVP_Main_Counting

namespace CyclotomicRankTwoSVP.Main
open scoped BigOperators

theorem syndrome_coset_gap (q k : ℕ) [Fact q.Prime]
    (hq : Odd q) (hk : 1 ≤ k) (hkq : 2 * k ≤ q) (h' : ℤ)
    (u : Fin k → ZMod q) (hu : compatible k h' u) :
    ∃ z₀ : ZMod q → ℤ, syndrome k z₀ = u ∧ coeffSum z₀ = h' ∧
      Set.BijOn (evalZ (q := q)) {z | syndrome k z = u ∧ coeffSum z = h'}
        {v | v - evalZ z₀ ∈ idealSet q k} ∧
      ∀ z : ZMod q → ℤ, syndrome k z = u → coeffSum z = h' →
        (binary z → ((Finset.univ.filter fun a => z a = 1).card : ℤ) = h' ∧
          N (evalZ z) = (h' : ℝ) * ((q : ℝ) - h')) ∧
        (¬ binary z → N (evalZ z) ≥ (h' : ℝ) * ((q : ℝ) - h') + 2 * q) := by sorry

end CyclotomicRankTwoSVP.Main
