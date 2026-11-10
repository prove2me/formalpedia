-- Prove2me | Theorems.Thm_FatFlat_Hereditary_lemma_4_2
-- name    : FatFlat.Hereditary.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:44:04.635221+00:00
-- url     : https://prove2.me/theorems/1808e4b7-87b7-4828-bf12-7c4ac0bb6d15
-- title:
--   Lemma 4.2 — drilling at most $h$ balls of radius 37 raises scatteredness from $2d$ to $2(d+1)$
-- statement:
--   Let $h,d,m$ be positive integers with $d\ge2$, let $G$ be a finite graph that does not contain the 1-subdivision of $K_h$ as a $(3d,6)$-shallow induced minor, and let $A\subseteq V(G)$ be a $2d$-scattered set with
--   $$|A|\ \ge\ \bigl(\max(4^5(h+1)^{10},\ m+h-1)\bigr)^{10^h}.$$
--   Then there are a set $X\subseteq V(G)$ with $|X|\le h$ and a set $B\subseteq A$ with $|B|\ge m$ that is $(2(d+1),\mathrm{Ball}_G(X,37))$-scattered in $G$: any two distinct vertices of $B$ outside $\mathrm{Ball}_G(X,37)$ are at distance more than $2(d+1)$ in $G-\mathrm{Ball}_G(X,37)$.
--
--   Differences from the source: none.
-- source:
--   Filtser, Le, Mählmann, Ma. Pilipczuk, Mi. Pilipczuk, Fatness and Flatness, arXiv:2607.21474, Lemma 4.2, p. 13 (PDF p. 15). Verbatim: 'Lemma 4.2. Let h, d, m be positive integers with d ⩾ 2, G be a graph that does not contain the 1-subdivision of K_h as a (3d,6)-shallow induced minor, and A ⊆ V(G) be a 2d-scattered set in G of size at least |A| ⩾ (max(4^5(h+1)^10, m+h−1))^{10^h}. Then, there exists a set X ⊆ V(G) of size at most h and a set B ⊆ A of size at least m that is (2(d+1), Ball(X,37))-scattered in G.' PDF SHA-256: 757d7502abd8762f687daa2125d7908bd129bcf2f5d6d5cc1756b514302adaf1.

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Classes

set_option autoImplicit false

namespace FatFlat.Hereditary

/-- **Lemma 4.2** (arXiv:2607.21474, p. 13). Let `h, d, m` be positive integers with `d ≥ 2`,
`G` a graph that does not contain the 1-subdivision of `K_h` as a `(3d, 6)`-shallow induced
minor, and `A ⊆ V(G)` a `2d`-scattered set with `|A| ≥ (max(4^5 (h+1)^10, m+h−1))^{10^h}`.
Then there are `X ⊆ V(G)` with `|X| ≤ h` and `B ⊆ A` with `|B| ≥ m` such that `B` is
`(2(d+1), Ball(X, 37))`-scattered in `G`. -/
theorem lemma_4_2 (h d m : ℕ) (hh : 0 < h) (hd : 2 ≤ d) (hm : 0 < m) (V : Type) [Fintype V]
    (G : SimpleGraph V)
    (hG : ¬ IsShallowInducedMinorOneSubdiv (⊤ : SimpleGraph (Fin h)) G (3 * d) 6)
    (A : Finset V) (hA : IsScattered G (2 * d) (A : Set V))
    (hAcard : (max (4 ^ 5 * (h + 1) ^ 10) (m + h - 1)) ^ (10 ^ h) ≤ A.card) :
    ∃ X : Finset V, X.card ≤ h ∧ ∃ B : Finset V, B ⊆ A ∧ m ≤ B.card ∧
      IsScatteredOff G (2 * (d + 1)) (ball G (X : Set V) 37) (B : Set V) := by sorry

end FatFlat.Hereditary
