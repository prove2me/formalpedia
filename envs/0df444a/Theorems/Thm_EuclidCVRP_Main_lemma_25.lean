-- Prove2me | Theorems.Thm_EuclidCVRP_Main_lemma_25
-- name    : EuclidCVRP.Main.lemma_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:56.488058+00:00
-- url     : https://prove2.me/theorems/f97dd1fc-8fe9-411c-86db-5300a9310298
-- title:
--   Lemma 25 — few smooth flows
-- statement:
--   For every constant $A>0$ there is a constant $C>0$ such that the following holds. Let $0<\varepsilon\le1$, $n\ge1$, and let a square have $m\le A\log_2 n/\varepsilon$ portals. Fix, for every pairing graph $E$, a compact ordering of $E$. Then the valid pairing flows (support a pairing graph $E$, entries at most $2n$) that are smooth with respect to the fixed ordering of their support form a finite set of size at most
--
--   $$n^{\,C(1/\varepsilon)^C}=n^{\mathrm{poly}(1/\varepsilon)}.$$
--
--   This bounds the number of dynamic-programming cells of the q-path PTAS.
--
--   Differences from the source:
--   - generalization: smooth w.r.t. the ordering given by Lemma 23 → smooth w.r.t. any choice of a compact ordering of each pairing graph; reason: the algorithm of Lemma 23 outputs a compact ordering, so this specializes to it
--   - reading: m = O((1/ε) log n) portals per square; n^{poly(1/ε)} → m ≤ A log₂ n/ε with C depending only on A; bound n^{C (1/ε)^C}; reason: pins the constant of m′ = O((1/ε) log n) and the polynomial
--   - encoding: n non-terminals → n ≥ 1; reason: the bound n^{…} is meaningless for n = 0 (0^x = 0)
--   - reading: ε > 0 (sufficiently small, p. 6) → ε ≤ 1; reason: within the paper's standing convention ε < 1/2 (p. 6)
--   - encoding: the number of smooth flows → the set of pairs (support, flow) is finite and its ncard is bounded; reason: finiteness is stated so that ncard is the cardinality
-- source:
--   Jannis Blauth, Fabrizio Grandoni, Bence Mátravölgyi, Ramin Mousavi, Kinter Ren, Mohammad R. Salavatipour, STOC 2027 submission #1236 (October 2026), p. 27, Lemma 25 (with Definition 24)

import Mathlib
import Definitions.Def_EuclidCVRP_Main_Pairing

set_option autoImplicit false

namespace EuclidCVRP.Main

/-- **Lemma 25** (p. 27). The number of smooth flows for a given square is at most `n^{poly(1/ε)}`:
for squares with `m = O((1/ε) log n)` portals (`m ≤ A log₂ n / ε`), and for every choice of a compact
ordering of each pairing graph, the valid pairing flows that are smooth with respect to the chosen
ordering of their support form a finite set of size at most `n^{C (1/ε)^C}`, with `C` depending only
on `A`. -/
theorem lemma_25 :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, (m : ℝ) ≤ A * Real.logb 2 n / ε →
        ∀ ord : Finset PEdge → List PEdge,
          (∀ E, IsPairingGraph m E → IsCompactOrdering m E (ord E)) →
          {p : Finset PEdge × (PEdge → ℕ) | IsValidFlow m n p.1 p.2 ∧ IsSmooth ε (ord p.1) p.2}.Finite ∧
          ({p : Finset PEdge × (PEdge → ℕ) | IsValidFlow m n p.1 p.2 ∧
              IsSmooth ε (ord p.1) p.2}.ncard : ℝ) ≤ (n : ℝ) ^ (C * (1 / ε) ^ C) := by sorry

end EuclidCVRP.Main
