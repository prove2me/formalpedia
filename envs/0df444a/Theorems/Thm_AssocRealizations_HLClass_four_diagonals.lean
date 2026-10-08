-- Prove2me | Theorems.Thm_AssocRealizations_HLClass_four_diagonals
-- name    : AssocRealizations.HLClass.four_diagonals
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:21.379227+00:00
-- url     : https://prove2.me/theorems/46e82e68-2d24-4fc1-80fe-a5c0a1187bca
-- title:
--   Proof of Theorem 4.9, pp. 17–18 — the diagonals crossing every parallel pair join {0,1} to {n+1,n+2}
-- statement:
--   Let $\sigma \in \{+,-\}^{n-1}$ and let $\delta$ be a diagonal of $P_{n+3}(\sigma)$. Then $\delta$ crosses at least one diagonal of every pair of diagonals with opposite normal vectors if and only if $\delta$ joins a vertex labelled $0$ or $1$ to a vertex labelled $n+1$ or $n+2$, i.e. $\delta$ is one of
--   $$\{0, n+1\},\quad \{0, n+2\},\quad \{1, n+1\},\quad \{1, n+2\}.$$
--
--   This step of the proof of Theorem 4.9 identifies a set of diagonals that any normal isomorphism must preserve; it is what pins the induced dihedral symmetry down to a reflection-reversal of $\widetilde\sigma$.
--
--   **Formalization Note** The page says that there are exactly four such diagonals. When $\sigma$ is constant one of the four pairs is a polygon edge of $P_{n+3}(\sigma)$, not a diagonal ($\{0,n+2\}$ for $\sigma = (-,\dots,-)$, $\{1,n+1\}$ for $\sigma = (+,\dots,+)$), and only three diagonals qualify. The statement is therefore the corrected one: the qualifying diagonals are exactly those of the four pairs that are diagonals. The theorem itself is unaffected.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, pp. 17–18, proof of Theorem 4.9 (corrected: only those of the four pairs that are diagonals)

import Mathlib
import Definitions.Def_AssocRealizations_HLClass_Setting

namespace AssocRealizations.HLClass

open ChvatalArtGallery.FanPartition

/-- Proof of Theorem 4.9 (pp. 17–18), the four diagonals, in corrected form: a diagonal of
`P_{n+3}(σ)` crosses at least one diagonal of every parallel pair iff its endpoint labels are
one of `{0, n + 1}`, `{0, n + 2}`, `{1, n + 1}`, `{1, n + 2}` (only those of the four that are
diagonals of `P_{n+3}(σ)`; for constant σ one of them is a polygon edge). -/
theorem four_diagonals (n : ℕ) (σ : Fin (n - 1) → Bool) (e : Sym2 (Fin (n + 3)))
    (he : IsDiagonal e) :
    (∀ f g : Sym2 (Fin (n + 3)), IsDiagonal f → IsDiagonal g →
        AssocRealizations.TypesMeet.Opposite (hlVec n σ f) (hlVec n σ g) → Crosses e f ∨ Crosses e g) ↔
      ∃ a b : Fin (n + 3), e = s(a, b) ∧ (hlLabel n σ a).val ≤ 1 ∧
        n + 1 ≤ (hlLabel n σ b).val := by sorry

end AssocRealizations.HLClass
