-- Prove2me | Theorems.Thm_DynBrooks_lemma_3_1
-- name    : DynBrooks.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:09:54.738681+00:00
-- url     : https://prove2.me/theorems/50319df7-3645-4233-a736-1157fcf7e41a
-- title:
--   Lemma 3.1 — list coloring of a connected non-Gallai graph from degree lists in linear time
-- statement:
--   Let $F$ be a connected graph that is not a Gallai tree, and let $L(v)\subseteq[\Delta]$ be explicit lists satisfying $|L(v)|\ge d_F(v)$ for every vertex $v$. A proper coloring of $F$ from these lists can be found in time
--
--   $$O\Bigl(|V(F)|+|E(F)|+\sum_{v\in V(F)}|L(v)|\Bigr),$$
--
--   using a preallocated temporary color-mark array.
--
--   Precisely: there are a program $P$ of the word-RAM and constants $C,W_0$ such that for every such $F$ on $N$ vertices, every $\Delta$, all lists, every edge listing, every word size $w\ge W_0(\lceil\log_2(N+\Delta)\rceil+1)$ and every coin tape, the run of $P$ on the instance halts within $C(N+|E(F)|+\sum_v|L(v)|)$ steps, having written colors $\chi(0),\dots,\chi(N-1)$ with $\chi(v)\in L(v)$ for all $v$ and $\chi(u)\ne\chi(v)$ for every edge $uv$.
--
--   This is the degree-list routine used by the repair regions of §5 and the reserved subgraphs of §6.
--
--   Differences from the source:
--   - encoding: time on an unspecified word-RAM, explicit lists → steps of one program of DynBrooks.Machine, on every coin tape, on the input layout of DynBrooks.ListColoring (arbitrary edge listing and list orders), output as N written words; reason: a concrete representation of the same algorithmic claim; the routine is deterministic (p.14)
--   - encoding: a preallocated temporary color-mark array → the memory is all zero at the start of the run; reason: the zero memory is a cleared array of every size, available at no cost, which is what 'preallocated' grants
--   - encoding: O(log n)-bit words → every word size w ≥ W₀(⌈log₂(N + ∆)⌉ + 1); reason: a word must hold a vertex and a color; this is the logarithmic word size of the instance
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), Lemma 3.1, p.14 (PDF 16)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynBrooks_ListColoring
import Definitions.Def_DynBrooks_Gallai

namespace DynBrooks

/-- **Lemma 3.1** (Mishra, Mukherjee, *Fully Dynamic Brooks Coloring*, STOC 2027 submission,
sha256 6542a9f1…, p.14 (PDF 16)). Let `F` be a connected graph that is not a Gallai tree, and let
`L(v) ⊆ [∆]` be explicit lists with `|L(v)| ≥ d_F(v)` for every vertex `v`. A proper coloring from
these lists can be found in time `O(|V(F)| + |E(F)| + Σ_v |L(v)|)`, using a preallocated temporary
color-mark array.

**Formalization Note.** One program `P` of the word-RAM (`DynBrooks.Machine`) and one constant `C`
work for every instance and every word size `w ≥ W₀(⌈log₂(N + ∆)⌉ + 1)` and every coin tape. The input
layout is `listWords` (an arbitrary edge listing and arbitrary list orders); the initial all-zero
memory is the preallocated mark array. Within `C(N + |E| + Σ|L(v)|)` steps the machine halts, having
written exactly the colors `χ(0), …, χ(N − 1)`, with `χ(v) ∈ L(v)` and `χ` proper on `F`. -/
theorem lemma_3_1 :
    ∃ C W₀ : ℕ, ∃ P : Program,
      ∀ (N Δ : ℕ) (F : SimpleGraph (Fin N)) [DecidableRel F.Adj], F.Connected → ¬ IsGallaiTree F →
      ∀ Lst : Fin N → List ℕ,
        (∀ v, (Lst v).Nodup ∧ (∀ c ∈ Lst v, 1 ≤ c ∧ c ≤ Δ) ∧ F.degree v ≤ (Lst v).length) →
      ∀ es : List (Fin N × Fin N), IsEdgeListing F es →
      ∀ w : ℕ, W₀ * (Nat.clog 2 (N + Δ) + 1) ≤ w → ∀ ω : ℕ → BitVec w,
        ∃ t ≤ C * (N + es.length + ∑ v, (Lst v).length), ∃ χ : Fin N → ℕ,
          Halted P (run P ω (listStart w Δ es Lst) t) ∧
          (run P ω (listStart w Δ es Lst) t).output = List.ofFn χ ∧
          (∀ v, χ v ∈ Lst v) ∧ ∀ u v, F.Adj u v → χ u ≠ χ v := by sorry

end DynBrooks
