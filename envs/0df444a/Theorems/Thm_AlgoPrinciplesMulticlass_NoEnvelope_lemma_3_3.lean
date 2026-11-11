-- Prove2me | Theorems.Thm_AlgoPrinciplesMulticlass_NoEnvelope_lemma_3_3
-- name    : AlgoPrinciplesMulticlass.NoEnvelope.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:29:04.818287+00:00
-- url     : https://prove2.me/theorems/b2cbea36-c75b-45b0-a6e7-efbf26f14fda
-- title:
--   Lemma 3.3 — on T_d, a class realizes the full cube on some block or misses a pattern along an infinite path
-- statement:
--   Fix $d\ge1$ and the tree $T_d$ of the §3.1 construction, with blocks $E_{d,v}=\{x_{d,v,j}:j\in[d]\}$, and identify $c\in\{0,1\}^d$ with the function $x_{d,v,j}\mapsto c(j)$ on $E_{d,v}$. For every class $F\subseteq Y^X$, at least one of the following holds.
--
--   *Condition 1.* There is a node $v\in T_d$ such that
--   $$\forall c\in\{0,1\}^d\ \exists f_c\in F:\ f_c{\restriction}E_{d,v}=c .$$
--
--   *Condition 2.* There is an infinite sequence $b_1,b_2,\dots$ with $b_i\in\{0,1\}^d$ such that for every $i\ge1$
--   $$b_i\notin F{\restriction}E_{d,(b_1,\dots,b_{i-1})}.$$
--
--   In the paper $F=\operatorname{im}(A)$ for a PAC learner $A$ of $\mathcal H$; the dichotomy is then split: Condition 1 forces $\mathrm{DS}(\operatorname{im}(A))\ge d$ and Condition 2 contradicts the PAC guarantee.
--
--   **Formalization Note.** Nodes are lists of vectors `Fin d → Bool`; Condition 2's sequence is `b : ℕ → Fin d → Bool` with `b 0` $=b_1$, and the node $(b_1,\dots,b_{i-1})$ is `List.ofFn fun k : Fin i => b k`.
--
--   Differences from the source:
--   - generalization: im(A) for the fixed PAC learner A of H → an arbitrary class F ⊆ Y^X; reason: the proof never uses that F is an image; taking F = im(A) gives the source's statement
--   - encoding: nodes (b_1, …, b_k), [d], {0,1}^d and the sequence b_1, b_2, … → `List (Fin d → Bool)`, `Fin d` (0-based), `Fin d → Bool`, `b : ℕ → Fin d → Bool` with `b 0` = b_1; reason: Lean convention; same objects
-- source:
--   Asilis, Dughmi, Sharan, Sun, Teng, Wang, Algorithmic Principles For Multiclass Learning Are Hard To Come By, STOC 2027 submission (manuscript sha256 03e91e8f…), p. 18, Lemma 3.3

import Mathlib
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_Construction

namespace AlgoPrinciplesMulticlass.NoEnvelope

/-- Lemma 3.3 (p. 18), for an arbitrary class `F ⊆ Y^X` in place of `im(A)`: for every `d ≥ 1`,
either some block `E_{d,v}` of `T_d` has every `c ∈ {0,1}^d` realized by a member of `F`
(Condition 1), or there is an infinite path `b₁, b₂, …` in `T_d` with `bᵢ` not realized by `F`
on the block of `(b₁, …, b_{i−1})` for every `i` (Condition 2). -/
theorem lemma_3_3 (F : Set (Pt → Label)) (d : ℕ) (hd : 1 ≤ d) :
    Condition1 F d ∨ Condition2 F d := by sorry

end AlgoPrinciplesMulticlass.NoEnvelope
