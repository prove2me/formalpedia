-- Prove2me | Theorems.Thm_CellProbeTree_Matching_lemma_3_4
-- name    : CellProbeTree.Matching.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:34:50.362445+00:00
-- url     : https://prove2.me/theorems/1954d67b-efb9-4f10-a7e4-96d38ae93732
-- title:
--   Lemma 3.4 — publication and simulation: encoding length (20) and residual footprints (21)
-- statement:
--   Let $s \ge 0$ cells of $w$ bits be given, and let $A \subseteq [s]$ be a set of cells to publish.
--
--   1. (20) The addresses and contents of $A$ have a **sequentially decodable** (prefix-free) encoding of length
--   $$\lceil \log_2(s+1)\rceil + \Big\lceil \log_2 \binom{s}{|A|} \Big\rceil + |A|\,w .$$
--   2. If $\log_2(s+1) \le K_0 w$, then for $|A| \le a$ this length is at most $K_1 w(1+a)$, with $K_1$ depending only on $K_0$ (the paper's "$O(w(1+a))$ when $\log_2(s+1) = O(w)$").
--   3. For a deterministic size bound $a$, the encoding can be padded to the deterministic length $\max_{k \le a}\big(\lceil\log_2(s+1)\rceil + \lceil\log_2\binom{s}{k}\rceil + kw\big)$, still decodable on all sets of size at most $a$.
--   4. Serving published words from the header preserves all adaptive answers, and after successive publications $A_0, A_1, \dots$ one may choose simulators whose residual footprints satisfy, pointwise, (21)
--   $$\mathrm{Probe}_j = \mathrm{Probe}_0 \setminus A_{<j}, \qquad |\mathrm{Probe}_j| - |\mathrm{Probe}_{j+1}| = |\mathrm{Probe}_j \cap A_j|,$$
--   where $A_{<j} = A_0 \cup \dots \cup A_{j-1}$ and $\mathrm{Probe}_j$ is the set of distinct cells read by the $j$-th simulator.
--
--   Differences from the source:
--   - encoding: "sequentially decodable encoding" → `enc A M` is a bit list such that whenever `enc A M` is a prefix of `enc A' M'`, then $A = A'$ and $M = M'$ on $A$; reason: prefix-freeness plus recovery of the addresses and contents is what sequential decodability means.
--   - reading: "if $\log_2(s+1) = O(w)$, this is $O(w(1+a))$ bits" → for every $K_0$ there is $K_1$ with length $\le K_1 w(1+a)$ whenever $w \ge 1$, $|A| \le a$ and $\log_2(s+1) \le K_0 w$; reason: explicit form of the two $O(\cdot)$, with the second constant depending only on the first.
--   - reading: "can be padded to a deterministic published length" → padded length equal to the maximum of (20) over sizes $k \le a$, decodable (injective) on sets of size at most $a$; reason: the natural deterministic length.
--   - generalization: "one may choose simulators" for stage $j$ → one simulator `sim S vals` per original query tree, depending only on the published addresses $S$ and their values, used at stage $j$ with $S = A_{<j}$, for every sequence $(A_j)$ (which may depend on the memory); reason: taking the $j$-th simulator to be `sim` at $A_{<j}$ gives the paper's statement.
--   - encoding: $\mathrm{Probe}_j$ → the set (`toFinset`) of addresses on the simulator's transcript; the difference identity is stated in $\mathbb Z$; reason: distinct addresses after memoizing repeated reads; integer subtraction avoids truncation.
-- source:
--   Liang, Liu, Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality, STOC 2027 submission (manuscript sha256 0e5a8eb2…), p. 15, Lemma 3.4, equations (20), (21)

import Mathlib
import Definitions.Def_DynOracleConn_ProbeTree

namespace CellProbeTree.Matching

open DynOracleConn

/-- Lemma 3.4 (publication and simulation). (20) The addresses `A ⊆ [s]` and the contents of a
published cell set have a sequentially decodable (prefix-free) encoding of length
`⌈log₂(s+1)⌉ + ⌈log₂ binom(s, |A|)⌉ + |A|·w`; if `log₂(s+1) ≤ K₀ w`, this is at most
`K₁ w (1 + a)` for `|A| ≤ a`, with `K₁` depending only on `K₀`; it can be padded to a
deterministic length. Serving published words from the header preserves every adaptive answer,
and after publications `A_0, A_1, …` there are simulators whose distinct-address footprints satisfy
(21): `Probe_j = Probe_0 \ A_{<j}` and `|Probe_j| − |Probe_{j+1}| = |Probe_j ∩ A_j|`. -/
theorem lemma_3_4 :
    -- (20): a sequentially decodable encoding of the addresses and contents
    (∀ s w : ℕ, ∃ enc : Finset (Fin s) → (Fin s → BitVec w) → List Bool,
      (∀ A M, (enc A M).length =
        Nat.clog 2 (s + 1) + Nat.clog 2 (s.choose A.card) + A.card * w) ∧
      (∀ A M A' M', enc A M <+: enc A' M' → A = A' ∧ ∀ c ∈ A, M c = M' c)) ∧
    -- if log₂(s+1) = O(w), the length is O(w(1 + a))
    (∀ K₀ : ℝ, ∃ K₁ : ℝ, ∀ s w a k : ℕ, 1 ≤ w → k ≤ a →
      Real.logb 2 ((s : ℝ) + 1) ≤ K₀ * w →
        ((Nat.clog 2 (s + 1) + Nat.clog 2 (s.choose k) + k * w : ℕ) : ℝ) ≤ K₁ * w * (1 + a)) ∧
    -- padding to a deterministic length
    (∀ s w a : ℕ, ∃ enc : Finset (Fin s) → (Fin s → BitVec w) → List Bool,
      (∀ A M, A.card ≤ a → (enc A M).length =
        (Finset.range (a + 1)).sup
          (fun k => Nat.clog 2 (s + 1) + Nat.clog 2 (s.choose k) + k * w)) ∧
      (∀ A M A' M', A.card ≤ a → A'.card ≤ a → enc A M = enc A' M' →
        A = A' ∧ ∀ c ∈ A, M c = M' c)) ∧
    -- simulation: answers preserved, footprints (21)
    (∀ (s w : ℕ) {Ans : Type} (T : ProbeTree (Fin s) (BitVec w) Ans),
      ∃ sim : (S : Finset (Fin s)) → (↥S → BitVec w) → ProbeTree (Fin s) (BitVec w) Ans,
        ∀ (M : Fin s → BitVec w) (A : ℕ → Finset (Fin s)),
          let S : ℕ → Finset (Fin s) := fun j => (Finset.range j).biUnion A
          let probe : ℕ → Finset (Fin s) := fun j =>
            ((ProbeTree.transcript (sim (S j) (fun c => M c.1)) M).map Prod.fst).toFinset
          ∀ j : ℕ,
            ProbeTree.run (sim (S j) (fun c => M c.1)) M = ProbeTree.run T M ∧
            probe j = ((ProbeTree.transcript T M).map Prod.fst).toFinset \ S j ∧
            ((probe j).card : ℤ) - (probe (j + 1)).card = (probe j ∩ A j).card) := by sorry

end CellProbeTree.Matching
