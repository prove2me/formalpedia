-- Prove2me | Theorems.Thm_DirKECC1549_Main_Supplement_claim_3
-- name    : DirKECC1549.Main.Supplement.claim_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:22:25.373941+00:00
-- url     : https://prove2.me/theorems/c886443e-f625-4691-84d8-b47c9ccb1890
-- title:
--   Claim 3 — J_k has at least h·3^ℓ k-vertex-connected components of size ℓ + 1
-- statement:
--   Let $k\ge7$, $\ell=\lfloor (k-1)/3\rfloor$, $h=k+2-3\ell$, and let $J_k$ be the graph of Claim 2. Then $J_k$ contains at least $h\,3^{\ell}$ distinct $k$-vertex-connected components, each of size $\ell+1$:
--   $$h\,3^{\ell}\ \le\ \big|\{K\in C_k(J_k):|K|=\ell+1\}\big|.$$
--
--   These components are the building blocks of the lower bound of Theorem 10.
--
--   **Formalization Note** Components are inclusion-maximal in the whole of $J_k$.
--
--   Differences from the source:
--   - encoding: undirected graph J_k on U ∪ B → SimpleGraph (Fin (k + 2)) with U = {0, …, 3ℓ − 1}, x_{i,j} = 3i + j, and B = {3ℓ, …, k + 1}; reason: a labeling of the k + 2 vertices; same graph
--   - encoding: at least h3^ℓ distinct components, each of size ℓ + 1 → h·3^ℓ ≤ the number of components of cardinality ℓ + 1; reason: the same count
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Claim 3, p.36 (J_k defined on p.35)

import Mathlib
import Definitions.Def_DirKECC1549_Main_Supplement_Undirected

set_option autoImplicit false

open Finset

namespace DirKECC1549.Main.Supplement

/-- Claim 3, p.36: for `k ≥ 7`, the graph `J_k` contains at least `h·3^ℓ` distinct
`k`-vertex-connected components of size `ℓ + 1` (`ℓ = ⌊(k − 1)/3⌋`, `h = k + 2 − 3ℓ`). -/
theorem claim_3 (k : ℕ) (hk : 7 ≤ k) :
    hB k * 3 ^ ell k ≤ ((kvccFamily k (Jk k)).filter (fun K => K.card = ell k + 1)).card := by sorry

end DirKECC1549.Main.Supplement
