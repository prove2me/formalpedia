-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_traversedBy_of_text_eq
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.traversedBy_of_text_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:45.969517+00:00
-- url     : https://prove2.me/theorems/23d541b9-850a-4366-8203-cb123a71b03f
-- title:
--   Block Deletion: traversed By of text eq
-- statement:
--   Let `o₁` be a traversing occurrence and `z` its last `upperCutLength` letters. If `z` also
--   ends at an upper anchor `p₂` of a word `l₂`, then the upper occurrence of `l₂` ending at `p₂`
--   traverses the edge too: its parse agrees with that of `o₁` on at least
--   `minDepth - k (N - 1) - 1 > startDepth` lower blocks, the anchors of `z` alone, which do not
--   depend on the context; and the length of its common suffix with the parse of the edge is a trie
--   node, hence at least `endDepth`. This is a statement about the original tuple.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L326-L529
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L326-L529

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Mathlib.Order.Nat
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)

theorem DeciSigma1.Holes.Fresh.BlockDeletion.traversedBy_of_text_eq [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    {o₁ : Fin k × ℕ × ℕ} (ho₁ : o₁ ∈ upperOccurrences W t) (hth : m.edge.TraversedBy o₁)
    {l₂ : Fin k} {p₂ : ℕ} (hp₂ : p₂ ∈ anchors W (t + 1) l₂) (hn : m.upperCutLength ≤ p₂)
    (hz : ((W l₂).drop (p₂ - m.upperCutLength)).take m.upperCutLength =
      ((W o₁.1).drop (o₁.2.2 - m.upperCutLength)).take m.upperCutLength) :
    m.edge.TraversedBy (l₂, upperOccurrenceStart W t l₂ p₂, p₂) := by sorry
