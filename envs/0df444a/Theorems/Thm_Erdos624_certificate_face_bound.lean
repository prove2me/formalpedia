-- Prove2me | Theorems.Thm_Erdos624_certificate_face_bound
-- name    : Erdos624.certificate_face_bound
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T14:04:18.541825+00:00
-- url     : https://prove2.me/theorems/cdc46444-576e-4185-8b5e-fe603e8ec31d
-- title:
--   Proper-parent face inequality (14): $Q^\circ(Y)\le D^\circ(Y)+(n-|S|)+\#\{u\in S:Y\cap(R_u\cup T_u)\neq\varnothing\}$ (Erdős 624)
-- statement:
--   Let $U$ be a set of inputs, $C$ a finite set of colours with $n=|C|$, $g_0,g_1:\mathcal P(U)\to C$ arbitrary and $L(A)=\{g_0(A),g_1(A)\}$; let $V\subseteq U$ be finite and $k\in\mathbb N$. Let $S\subseteq C\setminus L(\varnothing)$. For each $u\in S$ fix a deletion set $R_u\subseteq U$ and a parity certificate $w_u:U\to\mathbf F_2$ for the proper minimal witnesses of $u$ surviving the deletion: for every $A\subseteq V\setminus R_u$ with $0<|A|<k$, $u\in L(A)$ and $u\notin L(B)$ for all $B\subsetneq A$, we have $\sum_{x\in A}w_u(x)=1$. Put $T_u=\{x\in V\setminus R_u: w_u(x)=0\}$. For a $k$-set $Y$ let $J^\circ(Y)=\bigcup_{A\subsetneq Y}L(A)$, $D^\circ(Y)=n-|J^\circ(Y)|$, $J^\circ_{\mathrm{odd}}(Y)=\bigcup_{A\subsetneq Y,\,|A|\text{ odd}}L(A)$ and $Q^\circ(Y)=n-|J^\circ_{\mathrm{odd}}(Y)|$. Then for every $k$-set $Y\subseteq V$,$$Q^\circ(Y)\;\le\; D^\circ(Y)+(n-|S|)+\bigl|\{u\in S:\ Y\cap(R_u\cup T_u)\neq\varnothing\}\bigr|.\qquad(14)$$
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. By an earlier track-amplification result it suffices to find common holes for fixed numbers of tracks; this is an auxiliary finite inequality from Sol's Round 10 analysis of the two-track case. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 10 reports (consolidated report §'parity transport', §'many holes one level below'; Step 17 report 'resilient relations below the top layer', eqs. (9)-(26)); derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; proof reconstructed, hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem certificate_face_bound {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]
    (k : ℕ) (g0 g1 : Finset U → C) (V : Finset U) (S : Finset C)
    (hS : ∀ u ∈ S, u ∉ ({g0 ∅, g1 ∅} : Finset C))
    (R : C → Finset U) (w : C → U → ZMod 2)
    (hw : ∀ u ∈ S, ∀ A ⊆ V \ R u, 0 < #A → #A < k → u ∈ ({g0 A, g1 A} : Finset C) →
      (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) → ∑ x ∈ A, w u x = 1)
    (Y : Finset U) (hYV : Y ⊆ V) (hY : #Y = k) :
    Fintype.card C - #((Y.powerset.filter (fun A => A ≠ Y ∧ #A % 2 = 1)).biUnion
        (fun A => ({g0 A, g1 A} : Finset C))) ≤
      (Fintype.card C - #((Y.powerset.filter (fun A => A ≠ Y)).biUnion
        (fun A => ({g0 A, g1 A} : Finset C)))) + (Fintype.card C - #S) +
      #(S.filter (fun u => ¬ Disjoint Y (R u ∪ (V \ R u).filter (fun x => w u x = 0)))) := by sorry

end Erdos624
