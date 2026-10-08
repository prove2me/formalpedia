-- Prove2me | Theorems.Thm_BoundedDegreeST_LowerUpper_lemma_5_6
-- name    : BoundedDegreeST.LowerUpper.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:52.811511+00:00
-- url     : https://prove2.me/theorems/5de74fa5-1f4c-4bea-a844-f72e37936d5d
-- title:
--   Lemma 5.6 — every S ∈ 𝓛 keeps at least three tokens, and exactly three only if S is a special set or S = V
-- statement:
--   Throughout, $G=(V,E)$ is a finite simple graph, $F$ is a forest on $V$ with no edge in common with $E$, $A_v$ ($v\in U$) and $B_v$ ($v\in W$) are integer lower and upper degree bounds on subsets $U,W\subseteq V$, and $x^*$ is a basic feasible solution of LP-MBDCT$(G,\mathcal A,\mathcal B,U,W,F)$ with support $E^*=\{e: x^*_e\neq 0\}$. The forest $F$ is not a spanning tree. By Lemma 5.3 there are $T_U\subseteq U$, $T_W\subseteq W$ and a laminar family $\mathcal L$ of tight sets defining $x^*$; put $T=T_U\cup T_W$. As in the proof of Lemma 5.1, assume for contradiction that no edge has $x^*_e=1$ and no $v\in U\cup W$ has $\deg_{E^*}(v)=2$.Every active vertex $v$ holds $\deg_{E^*}(v)$ tokens.
--
--   **Lemma 5.6.** For every $S\in\mathcal L$, the tokens of the vertices of $S$ can be distributed so that every vertex of $T\cap S$ and every set of $\mathcal L$ strictly inside $S$ gets at least two tokens and $S$ gets at least three; and $S$ gets exactly three only if $S$ is a special set or $S=V$. In counting form:
--
--   $$
--   \operatorname{surplus}(S)=\sum_{v\in S}\deg_{E^*}(v)-2|T\cap S|-2\bigl|\{R\in\mathcal L:R\subsetneq S\}\bigr|\ \ge\ 3,
--   $$
--
--   and $\operatorname{surplus}(S)=3$ implies that $S$ is a special set or $S=V$.
--
--   The lemma is the counting step that, together with the rank count of Lemma 5.3, proves Lemma 5.1.
--
--   **Formalization Note** A distribution of fungible tokens with these lower bounds exists exactly when the surplus is at least the root's share, so "can distribute" is rendered as the counting inequality, and "gets exactly three tokens" as surplus equal to three. The rooted subtree is identified by its root $S\in\mathcal L$.
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, p. 669, Lemma 5.6

import Definitions.Def_BoundedDegreeST_LowerUpper_Tokens

namespace BoundedDegreeST.LowerUpper

/-- Singh–Lau, Lemma 5.6, p. 669, as a counting statement, in the setting of
§5.1 (see Claim 5.4), with `T = T_U ∪ T_W`. For every `S ∈ 𝓛`, the
`∑_{v ∈ S} deg_{E*}(v)` tokens of the vertices of `S` cover two tokens for every
vertex of `T ∩ S`, two for every member of `𝓛` strictly inside `S`, and at
least three for `S`; and the root gets exactly three only if `S` is a special
set or `S = V`. -/
theorem lemma_5_6
    {V : Type*} [Fintype V] [DecidableEq V]
    (E F : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (x : Sym2 V → ℝ) (L : Finset (Finset V)) (TU TW : Finset V)
    (hE : BoundedDegreeST.PlusOne.SimpleEdges E) (hF : BoundedDegreeST.PlusOne.IsForest F) (hEF : Disjoint E F)
    (hbasic : Basic E A B U W F x) (hnotree : ¬ BoundedDegreeST.PlusOne.IsSpanningTree F)
    (hbasis : DefinesBasis E A B U W F x L TU TW)
    (hnoone : ∀ e ∈ support E x, x e ≠ 1)
    (hnodeg2 : ∀ v ∈ U ∪ W, degree (support E x) v ≠ 2)
    (S : Finset V) (hS : S ∈ L) :
    3 ≤ surplus E x L (TU ∪ TW) S ∧
      (surplus E x L (TU ∪ TW) S = 3 →
        IsSpecialSet E x L (TU ∪ TW) S ∨ S = Finset.univ) := by sorry

end BoundedDegreeST.LowerUpper
