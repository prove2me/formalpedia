-- Prove2me | Theorems.Thm_CatalanHashing_Dynamic_theorem_1_3
-- name    : CatalanHashing.Dynamic.theorem_1_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:06:21.307528+00:00
-- url     : https://prove2.me/theorems/29bac013-c964-4da7-8bd8-168bdd9e332b
-- title:
--   Theorem 1.3 — anti-Robin-Hood Catalan hashing at load ≤ 1 − ε: 5 metadata bits per cell, expected scan cost ≤ |x|/ε for positive and ≤ 1 + 1/ε for negative queries
-- statement:
--   Let $\varepsilon\in(0,1)$ and let $S$ be a static set of items ($|x|\ge1$) stored in an $m$-cell table with load
--   $$\mathrm{load}(S)=\frac1m\sum_{x\in S}|x|\le1-\varepsilon,$$
--   the hashes $h(x)$ being independent and uniform. Anti-Robin-Hood Catalan hashing (ARCH) uses $O(1)$ bits of metadata per cell (the Catalan representation takes at most $2^5$ values per cell), and
--   $$\mathbb E[L_x]\le\frac{|x|}{\varepsilon}\quad\text{for every }x\in S,\qquad \mathbb E[D]\le1+\frac1\varepsilon,$$
--   where $L_x$ is the scan cost of the positive query for $x$ and $D$ that of a negative query for a key whose hash is uniform and independent of $S$.
--
--   The bound $|x|/\varepsilon$ is uniform in the item length, which is what lets the high-load dynamic construction of Section 8 use ARCH as its static part.
--
--   Differences from the source:
--
--   - encoding: h uniform on the continuous circle [0, m), canonical cell ⌊h(x)⌋ → h uniform on [0, 1] (unitInterval), canonical cell ⌊m h(x)⌋ capped at m - 1; reason: rescaling by m; [0, 1] and [0, 1) differ by a null set, and the cap only acts on the null event h = 1
--   - reading: "uses O(1) bits of metadata per cell" → Fintype.card CellMeta ≤ 2^5, CellMeta = (5-valued tag) × (home bit) × (stop bit), the per-cell Catalan representation; reason: the proof of Theorem 1.1 (p. 13) and Section 3 give exactly this representation (a 3-bit tag, a home bit and a stop bit); an explicit 5 specialises O(1)
--   - reading: "hashes are compared cyclically" (p. 26; unwrapping a run at the empty cell before it, p. 8) → archKey: m h(x) measured forward from the first cell of the run containing c(x), the runs being those of the load characterisation (p. 17); reason: this is the unwrapping of p. 8; comparisons across different runs do not affect the placement
--   - reading: ties between equal hashes (ignored by the paper, footnote 3) → broken by an arbitrary fixed order of the items (mergeSort is stable on Finset.univ.toList); reason: ties have probability 0
--   - reading: the scan cost of the query procedure of Section 3 (Catalan parser with home and stop bits) → queryCost: the number of cells from c(k) through the first cell that is empty, is the last cell of the sought item, or is the last cell of another item with canonical cell c(k) carrying the stop bit (1 if c(k) is not a home cell); reason: these are the stopping rules of Section 3, evaluated on the placement; that the parser recognises them is Lemma A.1
--   - encoding: negative query for a key y not in S → expectation over (hashes of S) ⊗ (independent uniform hash of y); reason: the key is absent and its hash is independent of S
--   - encoding: cells {0, ..., m-1} indexed cyclically, words of x numbered 1..|x| → Fin m with the forward distance cdist, words numbered 0..|x|-1; reason: index base and cyclic arithmetic only
-- source:
--   Conway, Komlós, Kuszmaul, Catalan Hashing: Efficient Linear Probing for Variable-Length Items, arXiv:2611.05235 (copy sha256 e2048176…), p. 26, Theorem 1.3 (PDF 27; stated p. 4, PDF 5)

import Mathlib
import Definitions.Def_CatalanHashing_Dynamic_Static

open MeasureTheory
open scoped ENNReal

namespace CatalanHashing.Dynamic

/-- Theorem 1.3 (anti-Robin-Hood Catalan hashing). For `ε ∈ (0, 1)` and a static set of items in
an `m`-cell table at load at most `1 - ε`, with independent uniform hashes: ARCH stores 5 bits
of metadata per cell, a positive query for `x` has expected scan cost at most `|x|/ε`, and a
negative query (for a key with an independent uniform hash) at most `1 + 1/ε`. -/
theorem theorem_1_3 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (m : ℕ) [NeZero m] {ι : Type*}
    [Fintype ι] (len : ι → ℕ) (hlen : ∀ x, 1 ≤ len x)
    (hload : (∑ x, (len x : ℝ)) ≤ (1 - ε) * m) :
    Fintype.card CellMeta ≤ 2 ^ 5 ∧
    (∀ x : ι, ∫⁻ h : ι → unitInterval,
        (queryCost len (fun y => canonical m (h y)) (arch m len h) (some x) (canonical m (h x)) :
          ℝ≥0∞) ∂(Measure.pi fun _ => volume) ≤ ENNReal.ofReal (len x / ε)) ∧
    ∫⁻ p : (ι → unitInterval) × unitInterval,
        (queryCost len (fun y => canonical m (p.1 y)) (arch m len p.1) none (canonical m p.2) :
          ℝ≥0∞) ∂((Measure.pi fun _ => volume).prod volume) ≤ ENNReal.ofReal (1 + 1 / ε) := by sorry

end CatalanHashing.Dynamic
