-- Prove2me | Theorems.Thm_EFXCounterex_Submodular_lemma_3_1
-- name    : EFXCounterex.Submodular.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:45:29.689773+00:00
-- url     : https://prove2.me/theorems/824ec896-fbe2-4df1-8f68-80f18661ef36
-- title:
--   Lemma 3.1 — an EFX two-agent split of $P,P,Q,Q,R,x$ under $u$ puts $Px$ or $QR$ in a bundle of at least three goods
-- statement:
--   Let $P,Q,R$ be distinct types and $r$ one of the two $R$-goods. Suppose two distinct agents $i$ and $j$ divide the six goods $P,P,Q,Q,r,x$ into bundles $Y$ (agent $i$) and $Z$ (agent $j$), each of at least two goods, and the division is EFX between them under the pair valuations $u$: $u_i(Z\setminus\{g\})\le u_i(Y)$ for every $g\in Z$ and $u_j(Y\setminus\{g\})\le u_j(Z)$ for every $g\in Y$. Then $Y$ or $Z$ has at least three goods and contains $x$ together with a $P$-good, or a $Q$-good together with an $R$-good.
--
--   Differences from the source:
--   - encoding: goods M = {A1, A2, B1, B2, C1, C2, x, y}, agents N = {a, b, c} associated with types A, B, C; type-words such as Px, QR, BCCx, UVx; values of u_i and v_i in {0, …, 7} → goods Fin 8 (A1, A2, B1, B2, C1, C2 = 0, …, 5; x = gx = 6; y = gy = 7) with kind : Fin 8 → GoodKind (typ 0, typ 1, typ 2 = A, B, C); agents Fin 3 (a, b, c = 0, 1, 2), agent t associated with type typ t; type-words as statements about the kinds of goods; u, v valued in ℝ; reason: a naming of the same finite sets and the same numbers
--   - encoding: "Divide P, P, Q, Q, R, x between any two agents, giving each at least two goods" → distinct agents i ≠ j, disjoint Y (agent i) and Z (agent j) with Y ∪ Z = typeGoods P ∪ typeGoods Q ∪ {r, gx} for a good r of type R, 2 ≤ |Y|, 2 ≤ |Z|; reason: each occurrence of a type is a distinct good (§3.1.1): both P-goods, both Q-goods and one R-good
--   - reading: "this division is EFX between them under u" → u i (Z.erase g) ≤ u i Y for all g ∈ Z and u j (Y.erase g) ≤ u j Z for all g ∈ Y; reason: neither agent EFX-envies the other's bundle; the self-comparisons of Definition 2.1 hold automatically because u is monotone
-- source:
--   Akrami, Mackenzie, Mayorov, Mehlhorn, Srinivas, Suzuki, Weidenbach 2026, Counterexamples to EFX for Submodular and Subadditive Valuations, arXiv:2605.06451 (supplied manuscript, sha256 700243a1…), Lemma 3.1, p. 8

import Mathlib
import Definitions.Def_EFXCounterex_Submodular_Instance

namespace EFXCounterex.Submodular

/-- Lemma 3.1 (p. 8). Let `P, Q, R` be distinct types and `r` one of the two `R`-goods. Divide the
six goods `P, P, Q, Q, R, x` (both `P`-goods, both `Q`-goods, `r` and `x`) between two distinct
agents `i` (bundle `Y`) and `j` (bundle `Z`), each receiving at least two goods. If this division
is EFX between them under the pair valuations `u` (neither agent envies the other's bundle after
the removal of any single good from it), then some bundle of at least three goods contains a
`P`-good together with `x`, or a `Q`-good together with an `R`-good. -/
theorem lemma_3_1 (P Q R : Fin 3) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R)
    (r : Fin 8) (hr : kind r = .typ R)
    (i j : Fin 3) (hij : i ≠ j) (Y Z : Finset (Fin 8))
    (hdisj : Disjoint Y Z) (hunion : Y ∪ Z = typeGoods P ∪ typeGoods Q ∪ {r, gx})
    (hY : 2 ≤ Y.card) (hZ : 2 ≤ Z.card)
    (hi : ∀ g ∈ Z, u i (Z.erase g) ≤ u i Y)
    (hj : ∀ g ∈ Y, u j (Y.erase g) ≤ u j Z) :
    ∃ W ∈ ({Y, Z} : Finset (Finset (Fin 8))), 3 ≤ W.card ∧
      ((gx ∈ W ∧ ∃ p ∈ W, kind p = .typ P) ∨
        (∃ q ∈ W, ∃ r' ∈ W, kind q = .typ Q ∧ kind r' = .typ R)) := by sorry

end EFXCounterex.Submodular
