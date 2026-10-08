-- Prove2me | Theorems.Thm_BoundedDegreeST_LowerUpper_claim_5_4
-- name    : BoundedDegreeST.LowerUpper.claim_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:46.448771+00:00
-- url     : https://prove2.me/theorems/704462af-da2f-4af2-adda-c59d5542a009
-- title:
--   Claim 5.4 — a special supernode contains exactly one active vertex v, with v ∈ T and deg_{E*}(v) = 3
-- statement:
--   Throughout, $G=(V,E)$ is a finite simple graph, $F$ is a forest on $V$ with no edge in common with $E$, $A_v$ ($v\in U$) and $B_v$ ($v\in W$) are integer lower and upper degree bounds on subsets $U,W\subseteq V$, and $x^*$ is a basic feasible solution of LP-MBDCT$(G,\mathcal A,\mathcal B,U,W,F)$ with support $E^*=\{e: x^*_e\neq 0\}$. The forest $F$ is not a spanning tree. By Lemma 5.3 there are $T_U\subseteq U$, $T_W\subseteq W$ and a laminar family $\mathcal L$ of tight sets defining $x^*$; put $T=T_U\cup T_W$. As in the proof of Lemma 5.1, assume for contradiction that no edge has $x^*_e=1$ and no $v\in U\cup W$ has $\deg_{E^*}(v)=2$.
--
--   **Claim 5.4.** If a supernode $C$ (a component of $F$) is special, i.e. the excess tokens $\deg_{E^*}(v)-2[v\in T]$ of its active vertices sum to exactly one, then $C$ contains exactly one active vertex $v$, and
--
--   $$
--   v\in T\qquad\text{and}\qquad \deg_{E^*}(v)=3 .
--   $$
--
--   The claim identifies the only supernodes that contribute a single excess token in the counting argument.
--
--   **Formalization Note** No supernode is contracted: $C$ is a component of $F$ in the original graph. The contradiction hypotheses of §5.1 (no 1-edge, no $v\in U\cup W$ of support degree 2) and "$F$ is not a spanning tree" are explicit binders; the claim is false without them.
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, p. 668, Claim 5.4

import Definitions.Def_BoundedDegreeST_LowerUpper_Tokens

namespace BoundedDegreeST.LowerUpper

/-- Singh–Lau, Claim 5.4, p. 668, in the setting of §5.1: `x` is a basic
feasible solution, `F` is not a spanning tree, `(𝓛, T_U, T_W)` is as in
Lemma 5.3, `T = T_U ∪ T_W`, and (contradiction hypotheses) there is no 1-edge
and no `v ∈ U ∪ W` with `deg_{E*}(v) = 2`. A special supernode (excess exactly
one) contains exactly one active vertex `v`, and `v ∈ T` with
`deg_{E*}(v) = 3`. -/
theorem claim_5_4
    {V : Type*} [Fintype V] [DecidableEq V]
    (E F : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (x : Sym2 V → ℝ) (L : Finset (Finset V)) (TU TW : Finset V)
    (hE : BoundedDegreeST.PlusOne.SimpleEdges E) (hF : BoundedDegreeST.PlusOne.IsForest F) (hEF : Disjoint E F)
    (hbasic : Basic E A B U W F x) (hnotree : ¬ BoundedDegreeST.PlusOne.IsSpanningTree F)
    (hbasis : DefinesBasis E A B U W F x L TU TW)
    (hnoone : ∀ e ∈ support E x, x e ≠ 1)
    (hnodeg2 : ∀ v ∈ U ∪ W, degree (support E x) v ≠ 2)
    (C : Finset V) (hC : IsSpecialSupernode E F x (TU ∪ TW) C) :
    ∃ v ∈ C, Active E x v ∧ (∀ w ∈ C, Active E x w → w = v) ∧
      v ∈ TU ∪ TW ∧ degree (support E x) v = 3 := by sorry

end BoundedDegreeST.LowerUpper
