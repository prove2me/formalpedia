-- Prove2me | Theorems.Thm_CountingLLL_DetCount_equation_21
-- name    : CountingLLL.DetCount.equation_21
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:11.444104+00:00
-- url     : https://prove2.me/theorems/79f1d536-3ec7-45c3-8cd4-15a12ae7929a
-- title:
--   §4.2, equation (21) — telescoping identity for $Z_\Phi$
-- statement:
--   Let $\Phi=(V,\mathcal Q,\mathcal C)$ satisfy Condition 1.1. Enumerate the constraints as $c_1,\dots,c_m$ and let $\mathcal C_i=\{c_1,\dots,c_i\}$ for $0\le i\le m$ (so $\mathcal C_0=\emptyset$). Then
--   $$Z_\Phi=\Big(\prod_{v\in V}|Q_v|\Big)\mathbb P[\mathcal C]=\Big(\prod_{v\in V}|Q_v|\Big)\prod_{i=1}^m\mathbb P[c_i\mid\mathcal C_{i-1}]=\Big(\prod_{v\in V}|Q_v|\Big)\prod_{i=1}^m\big(1-r_{\mathcal C_i,c_i}\big).$$
--
--   This identity reduces approximate counting to estimating the $m$ constraint marginals $r_{\mathcal C_i,c_i}$.
--
--   Differences from the source:
--   - encoding: an enumeration c_1, …, c_m of C and C_i = {c_1, …, c_i} → a bijection e of Fin m with c_{i+1} = e i and C_i the image of {j < i}; reason: every enumeration is such a bijection; indices are 0-based
--   - encoding: uniform product measure P on Q and P[A | B] → counting ratio |{σ : A σ}| / |Q| and P[A ∧ B] / P[B]; reason: the same measure on a finite product; every conditioning event in the statement has positive probability under its hypotheses
--   - generalization: standing assumption q ≥ 2, k ≥ 2, D ≥ 1 (PDF 3) → not assumed; reason: the identity or conditional LLL bound uses only the stated hypotheses, which guarantee positive conditioning probabilities; every source instance is covered
--   - encoding: finite variables V and finite domains Q_v → V = Fin n and Q_v = Fin (q v), with q v ≥ 2; reason: every finite source variable space is relabelled bijectively; no constraint function or scope is restricted
--   - generalization: a finite set of constraints C → constraints indexed by Fin m, permitting equal scopes and predicates at different indices; reason: enumerating a source constraint set gives an instance with distinct indices; allowing repetitions preserves that full source case
-- source:
--   Hongyang Liu, Chunyang Wang, Yitong Yin, Yiyao Zhang, Can Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442 (October 2026), §4.2, equation (21), PDF p. 14 (printed p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_CSP

set_option autoImplicit false

namespace CountingLLL.DetCount

open CSP

/-- §4.2, equation (21): the telescoping identity. For an enumeration `c_1, …, c_m` of the
constraints (here `c_{i+1} = e i`) and prefixes `C_i = {c_1, …, c_i}` (`C_0 = ∅`),
`Z_Φ = (∏_v |Q_v|) P[C] = (∏_v |Q_v|) ∏_i P[c_i | C_{i−1}] = (∏_v |Q_v|) ∏_i (1 − r_{C_i,c_i})`,
for a formula satisfying Condition 1.1. -/
theorem equation_21 (Φ : CSP) (hΦ : Φ.Condition11) (e : Fin Φ.m ≃ Fin Φ.m) :
    let Cpre : ℕ → Finset (Fin Φ.m) :=
      fun i => (Finset.univ.filter (fun j : Fin Φ.m => j.val < i)).image e
    (Φ.ZPhi : ℝ) = (∏ v, (Φ.q v : ℝ)) * Φ.prob (Φ.SatAll Finset.univ) ∧
    (∏ v, (Φ.q v : ℝ)) * Φ.prob (Φ.SatAll Finset.univ) =
      (∏ v, (Φ.q v : ℝ)) * ∏ i : Fin Φ.m, Φ.condProb (Φ.Sat (e i)) (Φ.SatAll (Cpre i.val)) ∧
    (∏ v, (Φ.q v : ℝ)) * ∏ i : Fin Φ.m, Φ.condProb (Φ.Sat (e i)) (Φ.SatAll (Cpre i.val)) =
      (∏ v, (Φ.q v : ℝ)) * ∏ i : Fin Φ.m, (1 - Φ.r (Cpre (i.val + 1)) (e i)) := by sorry

end CountingLLL.DetCount
