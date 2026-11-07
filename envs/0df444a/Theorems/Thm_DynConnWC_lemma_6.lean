-- Prove2me | Theorems.Thm_DynConnWC_lemma_6
-- name    : DynConnWC.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:38:19.318373+00:00
-- url     : https://prove2.me/theorems/1bae29dc-b058-4449-a191-e5b5f0060ef0
-- title:
--   Lemma 6 — all upper trees heavy $\Rightarrow D(F_i)\le D(F_{i-1})-S_i/2$
-- statement:
--   Let $F_{\mathrm{lo}},F_{\mathrm{up}}$ be forests of a graph $G$ on $V$, and let `ok` be any predicate on the trees of $F_{\mathrm{lo}}$. Give the representative of each tree $P$ of $F_{\mathrm{lo}}$ weight $1$ if $P$ satisfies `ok` and $2$ otherwise, and every other vertex weight $0$. If every tree of $F_{\mathrm{up}}$ has mass at least $2$, then, with $S$ the number of trees satisfying `ok`,
--   $$D(F_{\mathrm{up}})\le D(F_{\mathrm{lo}})-\frac S2.$$
--   This is the counting step of the level structure: when no upper tree is light, the upper forest already has a smaller deficit.
--
--   Differences from the source:
--   - generalization: $C_i(P)\ne\bot$ with up-to-date weights → any predicate on lower trees, with the weights defined from it; reason: the counting never uses the predicate's meaning; it specializes to $C_i$'s answers
--   - encoding: heavy: mass greater than one → mass at least two; reason: weights are natural numbers
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), Lemma 6, p.8 (PDF 9)

import Mathlib
import Definitions.Def_DynConnWC_Algorithm

set_option autoImplicit false

namespace DynConnWC

open Classical in
/-- **Lemma 6 (Counting upper trees).** King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027 submission, sha256 9d16c13e…), p.8 (PDF 9).
"Suppose that F_{i−1}, F_i ⊆ G and that the weights are up to date. Let S_i be the number of lower
trees P for which C_i(P) ≠ ⊥. If every upper tree is heavy, then D(F_i) ≤ D(F_{i−1}) − S_i/2."

**Formalization Note.** `ok` is any predicate on lower trees, standing for `C_i(P) ≠ ⊥`; the weights
are the ones §3.2 defines from it, and heavy means mass at least two. -/
theorem lemma_6 {n : ℕ} (G : SimpleGraph (Fin n)) (Flo Fup : Finset (Sym2 (Fin n)))
    (hlo : IsForestSet Flo) (hup : IsForestSet Fup) (hsublo : SubG Flo G) (hsubup : SubG Fup G)
    (ok : Finset (Fin n) → Prop)
    (hheavy : ∀ T ∈ trees Fup, 2 ≤ mass (repWeight Flo ok) T) :
    (deficit G Fup : ℝ) ≤ (deficit G Flo : ℝ) - (((trees Flo).filter ok).card : ℝ) / 2 := by sorry

end DynConnWC
