-- Prove2me | Theorems.Thm_FatFlat_Hereditary_lemma_4_1
-- name    : FatFlat.Hereditary.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:44:16.481192+00:00
-- url     : https://prove2.me/theorems/9f5c2581-d2fc-4eb8-bd5e-782b9931b3b8
-- title:
--   Lemma 4.1 — one improvement step: a dense ball, a more scattered subset, or a $(3d,2)$-shallow induced 1-subdivided $K_h$
-- statement:
--   Let $h,d$ be positive integers with $d\ge2$, let $G$ be a finite graph, and let $A\subseteq V(G)$ be a $2d$-scattered set with $|A|\ge 4^5(h+1)^{10}$. Then at least one of the following holds:
--   1. there is $v\in V(G)$ with $|A\cap\mathrm{Ball}_G(v,d+6)|\ge|A|^{1/10}$;
--   2. there is $B\subseteq A$ with $|B|\ge|A|^{1/10}$ that is $2(d+1)$-scattered in $G$;
--   3. the 1-subdivision of $K_h$ is a $(3d,2)$-shallow induced minor of $G$ (branch sets of the $h$ original vertices of radius at most $3d$, of the subdivision vertices of radius at most $2$).
--
--   $|A|^{1/10}$ is the real power.
--
--   Differences from the source:
--   - encoding: |A|^{1/10} → (A.card : ℝ) ^ ((1 : ℝ) / 10), compared in ℝ with the cardinalities; reason: the real tenth root, as printed
-- source:
--   Filtser, Le, Mählmann, Ma. Pilipczuk, Mi. Pilipczuk, Fatness and Flatness, arXiv:2607.21474, Lemma 4.1, p. 12 (PDF p. 14). Verbatim: 'Lemma 4.1. Let h, d be positive integers with d ⩾ 2, let G be a graph, and A ⊆ V(G) be a 2d-scattered set in G of size at least 4^5(h+1)^10. Then, one of the following holds: • There exists v ∈ V(G) such that |A ∩ Ball_G(v, d+6)| ⩾ |A|^{1/10}. • There exists B ⊆ A of size at least |A|^{1/10} that is 2(d+1)-scattered in G. • There exists a (3d,2)-shallow induced model of the 1-subdivision of K_h in G.' PDF SHA-256: 757d7502abd8762f687daa2125d7908bd129bcf2f5d6d5cc1756b514302adaf1.

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Classes

set_option autoImplicit false

namespace FatFlat.Hereditary

/-- **Lemma 4.1** (arXiv:2607.21474, p. 12). Let `h, d` be positive integers with `d ≥ 2`, `G` a
graph and `A ⊆ V(G)` a `2d`-scattered set of size at least `4^5 (h+1)^10`. Then one of the
following holds: some `v` has `|A ∩ Ball_G(v, d+6)| ≥ |A|^{1/10}`; some `B ⊆ A` with
`|B| ≥ |A|^{1/10}` is `2(d+1)`-scattered; or `G` contains a `(3d, 2)`-shallow induced model of
the 1-subdivision of `K_h`. -/
theorem lemma_4_1 (h d : ℕ) (hh : 0 < h) (hd : 2 ≤ d) (V : Type) [Fintype V]
    (G : SimpleGraph V) (A : Finset V) (hA : IsScattered G (2 * d) (A : Set V))
    (hAcard : 4 ^ 5 * (h + 1) ^ 10 ≤ A.card) :
    (∃ v : V, (A.card : ℝ) ^ ((1 : ℝ) / 10) ≤ (((A : Set V) ∩ ball G {v} (d + 6)).ncard : ℝ)) ∨
    (∃ B : Finset V, B ⊆ A ∧ (A.card : ℝ) ^ ((1 : ℝ) / 10) ≤ (B.card : ℝ) ∧
      IsScattered G (2 * (d + 1)) (B : Set V)) ∨
    IsShallowInducedMinorOneSubdiv (⊤ : SimpleGraph (Fin h)) G (3 * d) 2 := by sorry

end FatFlat.Hereditary
