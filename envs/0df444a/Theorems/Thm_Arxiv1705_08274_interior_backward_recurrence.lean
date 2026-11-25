-- Prove2me | Theorems.Thm_Arxiv1705_08274_interior_backward_recurrence
-- name    : Arxiv1705_08274.interior_backward_recurrence
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T03:18:56.200952+00:00
-- url     : https://prove2.me/theorems/cab50a32-bb82-5c71-a7b3-0450efe82129
-- title:
--   Eqs. (35)-(37b): adding identical nodes, interior edits by backward recurrence
-- statement:
--   Let $s\ge1$ identical nodes each have symmetric response $R=\begin{bmatrix}T_n&R_f\\R_f&T_n\end{bmatrix}$. Let $Q_l$ be the response of the first $l$ nodes, built by adding one node at a time with eqs. (28) ($Q_1=R$), with every adding step admissible, and let $U_l$ be the matrix (28b) of the step that adds node $l$. Suppose the interface intensities $I^\pm_0,\dots,I^\pm_s$ satisfy the node relations $[I^-_{j-1};I^+_j]=R\,[I^-_j;I^+_{j-1}]$ for $j=1,\dots,s$. Then:
--
--   1. every $Q_l$, $l\le s$, is symmetric;
--   2. $[I^-_0;I^+_l]=Q_l[I^-_l;I^+_0]$ for $1\le l\le s$, in particular eq. (35) for $l=s$;
--   3. the interior intensities follow by backward recurrence (37a,b): $\begin{bmatrix}I^+_{l-1}\\I^-_{l-1}\end{bmatrix}=U_l\begin{bmatrix}I^-_l\\I^+_0\end{bmatrix}$ for $l=s,s-1,\dots,2$;
--   4. adding $2^k$ nodes one at a time gives the same response as $k$ doublings, whenever every step of both procedures is admissible.
--
--   Part 4 makes precise the paper's statement that the procedure "should theoretically give the identical exiting distribution as doubling for a homogeneous medium".
--
--   **Formalization Note** The exiting intensities (36a,b) are (34b,c) with $Q_n$ replaced by $Q_s$. By part 1, the doubling statement (34) applies to $Q_s$ unchanged. The closing remark that nodes may differ in width and properties is not included, because the adding formula (28), which uses the symmetric form (25b), does not give the response of a heterogeneous composite in general (see the mission report).
-- source:
--   B. D. Ganapol, A 1D Radiative Transfer Benchmark with Polarization via Doubling and Adding, arXiv:1705.08274v1 (2017), claim c007; Section I.E.2, eqs. (35), (36a,b), (37a), (37b), PDF pp. 16-18

import Mathlib
import Definitions.Def_Arxiv1705_08274_Basic

open Matrix

namespace Arxiv1705_08274

theorem interior_backward_recurrence {N : ℕ} (Tn Rf : Matrix (Dir N) (Dir N) ℝ)
    (s : ℕ) (hs : 1 ≤ s)
    (hadd : ∀ l, 1 ≤ l → l < s →
      CanAdd (addSeq (fromBlocks Tn Rf Rf Tn) l) (fromBlocks Tn Rf Rf Tn))
    (Ip Im : ℕ → Dir N → ℝ)
    (hnode : ∀ j, 1 ≤ j → j ≤ s →
      Sum.elim (Im (j - 1)) (Ip j) = fromBlocks Tn Rf Rf Tn *ᵥ Sum.elim (Im j) (Ip (j - 1))) :
    (∀ l, l ≤ s → IsSymmetricResponse (addSeq (fromBlocks Tn Rf Rf Tn) l)) ∧
    (∀ l, 1 ≤ l → l ≤ s →
      Sum.elim (Im 0) (Ip l) = addSeq (fromBlocks Tn Rf Rf Tn) l *ᵥ Sum.elim (Im l) (Ip 0)) ∧
    (∀ l, 2 ≤ l → l ≤ s →
      Sum.elim (Ip (l - 1)) (Im (l - 1)) =
        addRespU (addSeq (fromBlocks Tn Rf Rf Tn) (l - 1)) (fromBlocks Tn Rf Rf Tn) *ᵥ
          Sum.elim (Im l) (Ip 0)) ∧
    (∀ k : ℕ,
      (∀ l, 1 ≤ l → l < 2 ^ k →
        CanAdd (addSeq (fromBlocks Tn Rf Rf Tn) l) (fromBlocks Tn Rf Rf Tn)) →
      (∀ j, j < k →
        CanAdd (dblSeq (fromBlocks Tn Rf Rf Tn) j) (dblSeq (fromBlocks Tn Rf Rf Tn) j)) →
      addSeq (fromBlocks Tn Rf Rf Tn) (2 ^ k) = dblSeq (fromBlocks Tn Rf Rf Tn) k) := by sorry

end Arxiv1705_08274
