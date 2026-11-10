-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_lemma_15
-- name    : DistancePreserver934.Exact.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:38:42.904868+00:00
-- url     : https://prove2.me/theorems/6e9d9b66-7724-4df4-9889-c71cf662fd35
-- title:
--   Lemma 15 (good loyal edges) — half of the loyal edges have bounded local conflict
-- statement:
--   Here the context is the §5 standing context: $R$ is a demand set, $H$ is a minimal distance preserver of $(G,R)$ with $|V_H|\le n$, $|E_H|\le nd$ and $\lambda_H(q)\ge l$ for $q\in R$; Equation (5) $6\le r\le\min\{d^2,l\}$; and a loyal core on a nonempty $V^*$ satisfying Equation (6). All balls are in $H$, $n_x=|B_H(x,r)|$, and $m=|\Lambda^*_H|$.
--
--   There is an absolute constant $C>0$ such that some set $\Lambda'_H\subseteq\Lambda^*_H$ with
--   $$|\Lambda'_H|\ge\frac m2\ \Big(\ge\frac{nd}{80}\Big)$$
--   has, for every $e\in\Lambda'_H$ and every endpoint $x$ of $e$,
--   $$\lambda^*_H(x,r/2,D(e))\le C\,\frac{n_x}{d\sqrt r}.\tag{11}$$
--
--   The constant $C$ is one universal good-edge constant (not the induction constant of §6). These good edges are the ones localized in Lemma 16 and clustered in the proof of Lemma 10.
--
--   Differences from the source:
--   - encoding: O(·)/Ω(·) bound with an unspecified absolute constant → one explicit constant, quantified (∃) before every vertex type, graph, demand set and parameter; reason: this is the meaning of the source's absolute-constant O-notation; no instance changes
--   - encoding: the label D(e) = q of a private edge → the label set D(e) = {q} itself is used as the index of λ*; reason: for loyal edges D(e) is a singleton, so the two counts coincide
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, Lemma 15, printed p. 16 (PDF p. 17)

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Preservers
import Definitions.Def_DistancePreserver934_Exact_Essential
import Definitions.Def_DistancePreserver934_Exact_LoyalCore

namespace DistancePreserver934.Exact

open Classical

/-- Lemma 15 (good loyal edges), printed p.16 / PDF p.17.  Under the §5 context, Equation (5)
and Equation (6), there is `Λ'_H ⊆ Λ*_H` with `|Λ'_H| ≥ m/2` (hence `≥ nd/80`) such that for every
`e ∈ Λ'_H` and every endpoint `x` of `e`, `λ*_H(x, r/2, D(e)) ≤ C n_x / (d √r)` (Equation (11)), where
`C` is an absolute constant. -/
theorem lemma_15 : ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type) [Fintype V] (G H : SimpleGraph V) (R : Finset (Sym2 V)) (n : ℕ) (d l r : ℝ)
      (Vs : Finset V),
      Sec5Context G H R n d l → Eq5 d l r → Eq6 H R Vs n d →
      ∃ Λ' : Finset (Sym2 V), Λ' ⊆ coreEdges H R Vs ∧
        ((coreEdges H R Vs).card : ℝ) / 2 ≤ (Λ'.card : ℝ) ∧ (n : ℝ) * d / 80 ≤ (Λ'.card : ℝ) ∧
        ∀ e ∈ Λ', IsGoodEdge H R Vs d r C e := by sorry

end DistancePreserver934.Exact
