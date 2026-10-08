-- Prove2me | Theorems.Thm_BoundedDegreeST_LowerUpper_claim_5_8
-- name    : BoundedDegreeST.LowerUpper.claim_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:26.52561+00:00
-- url     : https://prove2.me/theorems/fa2bcbeb-2a26-4546-a1db-45d5737694b5
-- title:
--   Claim 5.8 — if S ∈ 𝓛 has r members then x*(D(S)) = r − 1
-- statement:
--   Let $G=(V,E)$ be a finite simple graph, $F$ a forest on $V$ edge-disjoint from $E$, $x^*$ a feasible solution of LP-MBDCT$(G,\mathcal A,\mathcal B,U,W,F)$ with support $E^*$, and $(\mathcal L,T_U,T_W)$ as in the conclusion of Lemma 5.3. For $S\in\mathcal L$, the members of $S$ are its children in the forest of $\mathcal L$ and the supernodes contained in $S$ but in no child, and $D(S)$ is the set of support edges joining two different members. If $S$ has $r$ members, then
--
--   $$
--   x^*(D(S)) = r-1 .
--   $$
--
--   The identity is what forces at least three fractional edges between the members when $r=3$ (case 2 of Lemma 5.6) and integrality of a single edge when $r=2$ (case 3).
--
--   **Formalization Note** Only feasibility, the forest property of $F$ and the conclusion of Lemma 5.3 are assumed, which is all the paper's proof uses. The paper's proof writes $|S\cap F|$ for $|F(S)|$. $r$ is the cardinality of the set of members, and the identity is stated in $\mathbb R$.
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, p. 669, Claim 5.8

import Definitions.Def_BoundedDegreeST_LowerUpper_Tokens

namespace BoundedDegreeST.LowerUpper

/-- Singh–Lau, Claim 5.8, p. 669: if `x` is feasible, `(𝓛, T_U, T_W)` is as in
Lemma 5.3 and `S ∈ 𝓛` has `r` members (its children in the forest of `𝓛`
and the supernodes inside `S` but in no child), then `x(D(S)) = r − 1`, where
`D(S)` is the set of support edges joining two different members of `S`. -/
theorem claim_5_8 {V : Type*} [Fintype V] [DecidableEq V]
    (E F : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (x : Sym2 V → ℝ) (L : Finset (Finset V)) (TU TW : Finset V)
    (hE : BoundedDegreeST.PlusOne.SimpleEdges E) (hF : BoundedDegreeST.PlusOne.IsForest F) (hEF : Disjoint E F)
    (hfeas : Feasible E A B U W F x)
    (hbasis : DefinesBasis E A B U W F x L TU TW)
    (S : Finset V) (hS : S ∈ L) :
    BoundedDegreeST.PlusOne.edgeSum x (crossing E F x L S) = ((members F L S).card : ℝ) - 1 := by sorry

end BoundedDegreeST.LowerUpper
