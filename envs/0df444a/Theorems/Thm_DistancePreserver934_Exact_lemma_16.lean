-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_lemma_16
-- name    : DistancePreserver934.Exact.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:38:35.527866+00:00
-- url     : https://prove2.me/theorems/d8fc886a-ed67-446a-aa4c-67586c9b00ab
-- title:
--   Lemma 16 (localizing one demand label)
-- statement:
--   Here the context is the §5 standing context: $R$ is a demand set, $H$ is a minimal distance preserver of $(G,R)$ with $|V_H|\le n$, $|E_H|\le nd$ and $\lambda_H(q)\ge l$ for $q\in R$; Equation (5) $6\le r\le\min\{d^2,l\}$; and a loyal core on a nonempty $V^*$ satisfying Equation (6). All balls are in $H$, $n_x=|B_H(x,r)|$, and $m=|\Lambda^*_H|$.
--
--   Fix $A\ge0$ and a good-edge constant $C_g$. There is $K>0$, depending only on $A$ and $C_g$, with the following property. Let $\Lambda'_H\subseteq\Lambda^*_H$ consist of edges satisfying Equation (11) with constant $C_g$, let $F\subseteq\Lambda'_H$, and choose an endpoint $x_e$ of every $e\in F$. If $N\ge0$,
--   $$n_{x_e}\le N\quad(e\in F),\qquad\operatorname{diam}_H(\{x_e:e\in F\})\le Ar,$$
--   then every demand $q\in R$ satisfies
--   $$|\{e\in F:D(e)=\{q\}\}|\le K\,\frac{N}{d\sqrt r}.\tag{12}$$
--
--   The statement covers $F=\emptyset$, $A=0$ and every choice of endpoints. It is applied with $A=4$ in the proof of Lemma 10.
--
--   Differences from the source:
--   - encoding: O(·)/Ω(·) bound with an unspecified absolute constant → one explicit constant, quantified (∃) before every vertex type, graph, demand set and parameter; reason: this is the meaning of the source's absolute-constant O-notation; no instance changes
--   - generalization: Λ'_H the good loyal edges supplied by Lemma 15 (|Λ'_H| ≥ m/2, Equation (11) with Lemma 15's constant C) → any Λ'_H ⊆ Λ*_H whose edges satisfy Equation (11) with an arbitrary constant C_g; K may depend on A and C_g; reason: the proof uses only (11) for the edges of F; Lemma 15's set and constant are a special case
--   - reading: n_{x_e} ≤ N with N unconstrained → additionally N ≥ 0; reason: N bounds ball volumes (each at least 1); N < 0 is possible only for F = ∅, where the O-bound with a negative right-hand side is meaningless
--   - encoding: the label D(e) = q of a private edge → the label set D(e) = {q} itself is used as the index of λ*; reason: for loyal edges D(e) is a singleton, so the two counts coincide
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, Lemma 16, printed p. 16 (PDF p. 17)

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Preservers
import Definitions.Def_DistancePreserver934_Exact_Essential
import Definitions.Def_DistancePreserver934_Exact_LoyalCore

namespace DistancePreserver934.Exact

open Classical

/-- Lemma 16 (localizing one demand label), printed p.16 / PDF p.17.  Fix `A ≥ 0` and a
good-edge constant `C_g` (the constant of Equation (11)).  Under the §5 context, Equation (5)
and Equation (6), let `Λ'_H ⊆ Λ*_H` consist of edges satisfying Equation (11) with constant `C_g`,
let `F ⊆ Λ'_H`, and choose an endpoint `x_e` of every `e ∈ F`.  If `n_{x_e} ≤ N` for `e ∈ F` and
`diam_H({x_e : e ∈ F}) ≤ A r`, then for every `q ∈ R`,
`|{e ∈ F : D(e) = {q}}| ≤ K N / (d √r)` (Equation (12)), with `K` depending only on `A`
(and `C_g`). -/
theorem lemma_16 : ∀ A : ℝ, 0 ≤ A → ∀ Cg : ℝ, ∃ K : ℝ, 0 < K ∧
    ∀ (V : Type) [Fintype V] (G H : SimpleGraph V) (R : Finset (Sym2 V)) (n : ℕ) (d l r : ℝ)
      (Vs : Finset V),
      Sec5Context G H R n d l → Eq5 d l r → Eq6 H R Vs n d →
      ∀ Λ' : Finset (Sym2 V), Λ' ⊆ coreEdges H R Vs → (∀ e ∈ Λ', IsGoodEdge H R Vs d r Cg e) →
      ∀ F : Finset (Sym2 V), F ⊆ Λ' → ∀ xe : Sym2 V → V, (∀ e ∈ F, xe e ∈ e) →
      ∀ N : ℝ, 0 ≤ N → (∀ e ∈ F, (vol H (xe e) r : ℝ) ≤ N) →
      DiamLE H (F.image xe) (A * r) →
      ∀ q ∈ R, ((F.filter (fun e => essSet H R e = {q})).card : ℝ) ≤
        K * N / (d * Real.sqrt r) := by sorry

end DistancePreserver934.Exact
