-- Prove2me | Theorems.Thm_BoundedDegreeST_LowerUpper_claim_5_7
-- name    : BoundedDegreeST.LowerUpper.claim_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:14.664978+00:00
-- url     : https://prove2.me/theorems/ee620176-4df0-40e6-8fde-2feae2233d7b
-- title:
--   Claim 5.7 — a set S ∈ 𝓛 with S ≠ V has |δ(S)| ≥ 2 in the support
-- statement:
--   Throughout, $G=(V,E)$ is a finite simple graph, $F$ is a forest on $V$ with no edge in common with $E$, $A_v$ ($v\in U$) and $B_v$ ($v\in W$) are integer lower and upper degree bounds on subsets $U,W\subseteq V$, and $x^*$ is a basic feasible solution of LP-MBDCT$(G,\mathcal A,\mathcal B,U,W,F)$ with support $E^*=\{e: x^*_e\neq 0\}$. The forest $F$ is not a spanning tree. By Lemma 5.3 there are $T_U\subseteq U$, $T_W\subseteq W$ and a laminar family $\mathcal L$ of tight sets defining $x^*$; put $T=T_U\cup T_W$. As in the proof of Lemma 5.1, assume for contradiction that no edge has $x^*_e=1$ and no $v\in U\cup W$ has $\deg_{E^*}(v)=2$.
--
--   **Claim 5.7.** For every $S\in\mathcal L$ with $S\neq V$,
--
--   $$
--   |\delta_{E^*}(S)|\ \ge\ 2 .
--   $$
--
--   The claim is used in Claim 5.9 to rule out a special set's cut having fewer than three edges.
--
--   **Formalization Note** In the paper $S$ is the root of a subtree of the forest of $\mathcal L$, so $S\in\mathcal L$; the cut is counted in the support $E^*$.
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, p. 669, Claim 5.7

import Definitions.Def_BoundedDegreeST_LowerUpper_Tokens

namespace BoundedDegreeST.LowerUpper

/-- Singh–Lau, Claim 5.7, p. 669, in the setting of §5.1 (see Claim 5.4): for a
set `S` of the laminar family `𝓛` with `S ≠ V`, at least two edges of the
support `E*` cross `S`. -/
theorem claim_5_7
    {V : Type*} [Fintype V] [DecidableEq V]
    (E F : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (x : Sym2 V → ℝ) (L : Finset (Finset V)) (TU TW : Finset V)
    (hE : BoundedDegreeST.PlusOne.SimpleEdges E) (hF : BoundedDegreeST.PlusOne.IsForest F) (hEF : Disjoint E F)
    (hbasic : Basic E A B U W F x) (hnotree : ¬ BoundedDegreeST.PlusOne.IsSpanningTree F)
    (hbasis : DefinesBasis E A B U W F x L TU TW)
    (hnoone : ∀ e ∈ support E x, x e ≠ 1)
    (hnodeg2 : ∀ v ∈ U ∪ W, degree (support E x) v ≠ 2)
    (S : Finset V) (hS : S ∈ L) (hSV : S ≠ Finset.univ) :
    2 ≤ (cut (support E x) S).card := by sorry

end BoundedDegreeST.LowerUpper
