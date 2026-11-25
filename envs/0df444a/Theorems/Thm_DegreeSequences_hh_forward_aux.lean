-- Prove2me | Theorems.Thm_DegreeSequences_hh_forward_aux
-- name    : DegreeSequences.hh_forward_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:56:18.810191+00:00
-- url     : https://prove2.me/theorems/9a96653e-f394-4f46-be44-7b3a73f79628
-- title:
--   Degree Sequences: hh forward aux
-- statement:
--   The Degree Sequences construction uses the hh forward aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L251-L301
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L251-L301

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.hh_forward_aux {m : ℕ} (d : Fin (m + 1) → ℕ) (hd : Antitone d) (h0 : d 0 ≤ m) (r : ℕ) :
    ∀ (G : SimpleGraph (Fin (m + 1))) (_ : DecidableRel G.Adj), (∀ i, G.degree i = d i) →
      #{v ∈ hhSet d | ¬ G.Adj 0 v} ≤ r →
      ∃ (G' : SimpleGraph (Fin (m + 1))) (_ : DecidableRel G'.Adj),
        (∀ i, G'.degree i = d i) ∧ ∀ v ∈ hhSet d, G'.Adj 0 v := by sorry
