-- Prove2me | Theorems.Thm_AssocRealizations_TypesMeet_theorem_6_1
-- name    : AssocRealizations.TypesMeet.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:28:15.736344+00:00
-- url     : https://prove2.me/theorems/4d92cb81-4182-4dea-884d-7b5f845e643e
-- title:
--   Theorem 6.1 — the CFZ associahedron is the only common normal-isomorphism class
-- statement:
--   Fix $n\ge0$. If a Hohlweg–Lange associahedron with sign sequence $\sigma\in\{+,-\}^{n-1}$ is normally isomorphic to a Santos associahedron with seed triangulation $T$, then $T$ is a dihedral image of the fixed snake triangulation. The alternating Hohlweg–Lange sign sequence also gives a fan normally isomorphic to the Santos snake fan:
--
--   $$\bigl(\operatorname{Fan}^{I}_n(\sigma)\cong_{\mathrm{lin}}\operatorname{Fan}^{II}_n(T)\bigr)
--   \Longrightarrow T=g(\operatorname{snake}_n),\qquad
--   \operatorname{Fan}^{I}_n(\sigma_{\mathrm{alt}})\cong_{\mathrm{lin}}\operatorname{Fan}^{II}_n(\operatorname{snake}_n).$$
--
--   Thus the Chapoton–Fomin–Zelevinsky associahedron is the unique normal-isomorphism class shared by the two families. **Formalization Note** The first assertion quantifies over every sign word and every seed triangulation; the dihedral symmetry acts on cyclic positions. Dimensions zero and one are included.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 28, Theorem 6.1; p. 4, Theorem 1.1

import Mathlib
import Definitions.Def_AssocRealizations_TypesMeet_Setting

namespace AssocRealizations.TypesMeet

open ChvatalArtGallery.FanPartition

theorem theorem_6_1 (n : ℕ) :
    (∀ (σ : Fin (n - 1) → Bool) (T : Finset (Sym2 (Fin (n + 3)))),
      IsTriangulation (n + 3) T →
      NormallyIsomorphic (hlFan σ) (santosFan T) →
      IsDihedralImage (snake n) T) ∧
    NormallyIsomorphic (hlFan (altSigma n)) (santosFan (snake n)) := by sorry
end AssocRealizations.TypesMeet
