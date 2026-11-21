-- Prove2me | Theorems.Thm_DetANN_Supplement_Thm32_dedup_set_spec
-- name    : DetANN.Supplement.Thm32.dedup_set_spec
-- status  : Proved
-- author  : @milia
-- created : 2026-11-21T03:40:11.391935+00:00
-- url     : https://prove2.me/theorems/03932c58-acdf-42ee-9090-0f17f6c9910e
-- title:
--   The dedupe table is the difference set of Theorem 3.2
-- statement:
--   Let $P:\mathrm{Fin}\,n\to\mathbb R^d$ be injective and let $\mathcal D$ be the finset of the list $\mathrm{ddList}(\mathrm{ptSeq}\,P,n)$ (definition `DetANN_Supplement_PreDedup`). Then
--   1. $0\notin\mathcal D$;
--   2. for distinct points $y\neq z$ of $P$, $y-z\in\mathcal D$ or $z-y\in\mathcal D$;
--   3. $|\mathcal D|$ equals the length of the list;
--   4. if $n\ge2$ then $|\mathcal D|\ge1$.
--
--   These are the hypotheses on $\mathcal D$ of `theorem_3_2_greedy`.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a proof of DetANN.Supplement.theorem_3_2 (Feng, Indyk, STOC 2027 submission, Theorem 3.2, p.7; the construction of §6.1, p.14, and Lemma 6.2). The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_Sylvester
import Definitions.Def_DetANN_SignedBlocks
import Definitions.Def_DetANN_Supplement_EvProg
import Definitions.Def_DetANN_Supplement_PreProg
import Definitions.Def_DetANN_Supplement_PreDedup

namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN

/-- **The dedupe table is the difference set of Theorem 3.2.** For injective `P`, the finset of
`ddList (ptSeq P) n` has no zero vector, contains `y - z` or `z - y` for all distinct points `y, z`,
has as many elements as the list has entries, and is nonempty when `n ≥ 2`. These are the hypotheses on
`𝒟` of `theorem_3_2_greedy`. -/
theorem dedup_set_spec :
    ∀ {d : ℕ} {n : ℕ} (P : Fin n → EuclideanSpace ℝ (Fin d)) (hP : Function.Injective P),
    (∀ v ∈ (ddList (ptSeq P) n).toFinset, v ≠ 0) ∧
    (∀ y ∈ Finset.univ.image P, ∀ z ∈ Finset.univ.image P, y ≠ z →
      y - z ∈ (ddList (ptSeq P) n).toFinset ∨ z - y ∈ (ddList (ptSeq P) n).toFinset) ∧
    (ddList (ptSeq P) n).toFinset.card = (ddList (ptSeq P) n).length ∧
    (2 ≤ n → 1 ≤ (ddList (ptSeq P) n).toFinset.card) := by sorry

end DetANN.Supplement.Thm32
