-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_lemma_17
-- name    : DistancePreserver934.Exact.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:38:35.907684+00:00
-- url     : https://prove2.me/theorems/8f9c8df8-3ffc-470e-a545-2519f1fd2592
-- title:
--   Lemma 17 — the weighted conflict sum $Z=O(m/(d\sqrt r))$
-- statement:
--   Here the context is the §5 standing context: $R$ is a demand set, $H$ is a minimal distance preserver of $(G,R)$ with $|V_H|\le n$, $|E_H|\le nd$ and $\lambda_H(q)\ge l$ for $q\in R$; Equation (5) $6\le r\le\min\{d^2,l\}$; and a loyal core on a nonempty $V^*$ satisfying Equation (6). All balls are in $H$, $n_x=|B_H(x,r)|$, and $m=|\Lambda^*_H|$.
--
--   There is an absolute constant $C_0>0$ such that
--   $$Z:=\sum_{x\in V^*}\ \sum_{e\in\Lambda^*_H,\ x\in e}\frac{\lambda^*_H(x,r/2,D(e))}{n_x}\le C_0\,\frac{m}{d\sqrt r}.\tag{13}$$
--
--   Both sums run over incidences $(x,e)$. Lemma 17 is the input of Lemmas 15 and 16.
--
--   Differences from the source:
--   - encoding: O(·)/Ω(·) bound with an unspecified absolute constant → one explicit constant, quantified (∃) before every vertex type, graph, demand set and parameter; reason: this is the meaning of the source's absolute-constant O-notation; no instance changes
--   - encoding: the label D(e) = q of a private edge → the label set D(e) = {q} itself is used as the index of λ*; reason: for loyal edges D(e) is a singleton, so the two counts coincide
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, Lemma 17, printed p. 16 (PDF p. 17)

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Preservers
import Definitions.Def_DistancePreserver934_Exact_Essential
import Definitions.Def_DistancePreserver934_Exact_LoyalCore

namespace DistancePreserver934.Exact

open Classical

/-- Lemma 17, printed p.16 / PDF p.17.  Under the §5 context, Equation (5) and Equation (6),
`Z = ∑_{x ∈ V*} ∑_{e ∈ Λ*_H, x ∈ e} λ*_H(x, r/2, D(e)) / n_x = O(m / (d √r))` (Equation (13)),
with `m = |Λ*_H|`, `n_x = |B_H(x, r)|`, and one absolute constant. -/
theorem lemma_17 : ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (V : Type) [Fintype V] (G H : SimpleGraph V) (R : Finset (Sym2 V)) (n : ℕ) (d l r : ℝ)
      (Vs : Finset V),
      Sec5Context G H R n d l → Eq5 d l r → Eq6 H R Vs n d →
      conflictSum H R Vs r ≤ C₀ * ((coreEdges H R Vs).card : ℝ) / (d * Real.sqrt r) := by sorry

end DistancePreserver934.Exact
