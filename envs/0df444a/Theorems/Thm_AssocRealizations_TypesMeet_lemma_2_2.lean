-- Prove2me | Theorems.Thm_AssocRealizations_TypesMeet_lemma_2_2
-- name    : AssocRealizations.TypesMeet.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:27:57.2799+00:00
-- url     : https://prove2.me/theorems/e82be7ae-b4eb-4c54-b5f0-f1e8d081e382
-- title:
--   Lemma 2.2 — automorphisms of associahedron diagonals are dihedral
-- statement:
--   Let $n\ge0$ and let $D$ be the diagonals of a cyclic $(n+3)$-gon. A bijection of unordered vertex pairs that maps diagonals to diagonals in both directions and preserves crossing of any two diagonals is induced, on $D$, by a single rotation or reflection of the polygon:
--
--   $$\pi(\{a,b\}) = \{r+\delta a,\ r+\delta b\},\quad \delta\in\{+1,-1\}\pmod{n+3}.$$
--
--   Moreover, for $n\ge2$ the pair $(r,\delta)$ is unique, so the $2n+6$ rotations and reflections act as distinct automorphisms and the automorphism group is the dihedral group of order $2n+6$. This is the diagonal form of the face lattice automorphism statement. It restricts the possible facet correspondence in a normal isomorphism. **Formalization Note** The bijection is defined on all unordered pairs, but its conclusion concerns only diagonals; the paper's face lattice is the complex of noncrossing diagonal sets. The second sentence of the lemma is rendered as the uniqueness of the inducing symmetry for $n\ge2$.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 6, Lemma 2.2

import Mathlib
import Definitions.Def_AssocRealizations_TypesMeet_Setting

namespace AssocRealizations.TypesMeet

open ChvatalArtGallery.FanPartition

theorem lemma_2_2 (n : ℕ)
    (π : Sym2 (Fin (n + 3)) ≃ Sym2 (Fin (n + 3)))
    (hdiag : ∀ e, IsDiagonal e ↔ IsDiagonal (π e))
    (hcross : ∀ e f, IsDiagonal e → IsDiagonal f →
      (Crosses e f ↔ Crosses (π e) (π f))) :
    ∃ r refl, (∀ e, IsDiagonal e → π e = Sym2.map (dihedral r refl) e) ∧
      (2 ≤ n → ∀ r' refl', (∀ e, IsDiagonal e → π e = Sym2.map (dihedral r' refl') e) →
        r' = r ∧ refl' = refl) := by sorry
end AssocRealizations.TypesMeet
