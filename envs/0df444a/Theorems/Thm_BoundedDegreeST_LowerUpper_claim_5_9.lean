-- Prove2me | Theorems.Thm_BoundedDegreeST_LowerUpper_claim_5_9
-- name    : BoundedDegreeST.LowerUpper.claim_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:13.649423+00:00
-- url     : https://prove2.me/theorems/8b074452-7749-40c5-9776-6f06f9db8304
-- title:
--   Claim 5.9 — a set S ≠ V with exactly three members, all special, and |D(S)| ≥ 3 is a special set
-- statement:
--   Throughout, $G=(V,E)$ is a finite simple graph, $F$ is a forest on $V$ with no edge in common with $E$, $A_v$ ($v\in U$) and $B_v$ ($v\in W$) are integer lower and upper degree bounds on subsets $U,W\subseteq V$, and $x^*$ is a basic feasible solution of LP-MBDCT$(G,\mathcal A,\mathcal B,U,W,F)$ with support $E^*=\{e: x^*_e\neq 0\}$. The forest $F$ is not a spanning tree. By Lemma 5.3 there are $T_U\subseteq U$, $T_W\subseteq W$ and a laminar family $\mathcal L$ of tight sets defining $x^*$; put $T=T_U\cup T_W$. As in the proof of Lemma 5.1, assume for contradiction that no edge has $x^*_e=1$ and no $v\in U\cup W$ has $\deg_{E^*}(v)=2$.
--
--   **Claim 5.9.** Let $S\in\mathcal L$ with $S\neq V$. If $S$ has exactly three members $R_1,R_2,R_3$, each of them special (a special supernode or a special set in the sense of Definition 5.5), and
--
--   $$
--   |D(S)|\ \ge\ 3,
--   $$
--
--   then $S$ is a special set.
--
--   The claim is the step of the induction in Lemma 5.6 that lets a set collecting only three tokens be special.
--
--   **Formalization Note** "Contains exactly three special members" is read as "has exactly three members, and all three are special": the proof computes $|\delta(S)|=\sum_i|\delta(R_i)|-2|D(S)|$, which needs the $R_i$ to be all the members, and case 2 of Lemma 5.6 applies the claim in that form. The proof's identity $\chi_{\delta(S)}=\sum_i\chi_{\delta(R_i)}+\sum_i\chi_{E(R_i)}-2\chi_{E(S)}$ has a misprinted coefficient; the identity that holds is $\chi_{\delta(S)}=\sum_i\chi_{\delta(R_i)}+2\sum_i\chi_{E(R_i)}-2\chi_{E(S)}$, and the conclusion is unchanged.
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, p. 669, Claim 5.9

import Definitions.Def_BoundedDegreeST_LowerUpper_Tokens

namespace BoundedDegreeST.LowerUpper

/-- Singh–Lau, Claim 5.9, p. 669, in the setting of §5.1 (see Claim 5.4), with
`T = T_U ∪ T_W`: if `S ∈ 𝓛`, `S ≠ V`, `S` has exactly three members, all
three special (each a special supernode or a special set), and `|D(S)| ≥ 3`,
then `S` is a special set (Definition 5.5). -/
theorem claim_5_9
    {V : Type*} [Fintype V] [DecidableEq V]
    (E F : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (x : Sym2 V → ℝ) (L : Finset (Finset V)) (TU TW : Finset V)
    (hE : BoundedDegreeST.PlusOne.SimpleEdges E) (hF : BoundedDegreeST.PlusOne.IsForest F) (hEF : Disjoint E F)
    (hbasic : Basic E A B U W F x) (hnotree : ¬ BoundedDegreeST.PlusOne.IsSpanningTree F)
    (hbasis : DefinesBasis E A B U W F x L TU TW)
    (hnoone : ∀ e ∈ support E x, x e ≠ 1)
    (hnodeg2 : ∀ v ∈ U ∪ W, degree (support E x) v ≠ 2)
    (S : Finset V) (hS : S ∈ L) (hSV : S ≠ Finset.univ)
    (hthree : (members F L S).card = 3)
    (hspecial : ∀ R ∈ members F L S, IsSpecialMember E F x L (TU ∪ TW) R)
    (hD : 3 ≤ (crossing E F x L S).card) :
    IsSpecialSet E x L (TU ∪ TW) S := by sorry

end BoundedDegreeST.LowerUpper
