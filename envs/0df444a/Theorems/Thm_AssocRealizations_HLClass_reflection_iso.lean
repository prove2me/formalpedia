-- Prove2me | Theorems.Thm_AssocRealizations_HLClass_reflection_iso
-- name    : AssocRealizations.HLClass.reflection_iso
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:51.977233+00:00
-- url     : https://prove2.me/theorems/e90a7dd0-219c-4317-9c67-59d48c6ddcad
-- title:
--   Proof of Theorem 4.9, p. 18 — Ass^I_n(σ) and Ass^I_n(−σ) are normally isomorphic
-- statement:
--   For every $\sigma \in \{+,-\}^{n-1}$:
--
--   1. the normal fans of $\mathrm{Ass}^I_n(\sigma)$ and $\mathrm{Ass}^I_n(-\sigma)$ are linearly isomorphic;
--   2. the family of sets $S_\delta(-\sigma)$, over the diagonals $\delta$, is the family of complements $[n+1] \setminus S_\delta(\sigma)$:
--   $$\{S_\delta(-\sigma) : \delta\} = \{[n+1] \setminus S_\delta(\sigma) : \delta\}.$$
--
--   Since $e_{[n+1]\setminus S} \equiv -e_S$ modulo $e_{[n+1]}$, the isomorphism is multiplication by $-1$. This is the reflection half of the "if" direction of Theorem 4.9.
--
--   **Formalization Note** The page writes $S_\delta(-\sigma) = [n] - S_\delta(\sigma)$; since $S_\delta \subseteq [n+1]$ the complement is taken in $[n+1]$. The identity holds for the families; diagonal by diagonal it goes through the mirror-image diagonal, because $P_{n+3}(\sigma)$ and $P_{n+3}(-\sigma)$ have different boundary edges.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 18, proof of Theorem 4.9, second paragraph (the printed [n] read as [n + 1])

import Mathlib
import Definitions.Def_AssocRealizations_HLClass_Setting

namespace AssocRealizations.HLClass

open ChvatalArtGallery.FanPartition

/-- Proof of Theorem 4.9 (p. 18): `Ass^I_n(σ)` and `Ass^I_n(-σ)` are normally isomorphic, and the
family of S-sets of `-σ` is the family of complements in `[n + 1]` of the S-sets of `σ`. -/
theorem reflection_iso (n : ℕ) (σ : Fin (n - 1) → Bool) :
    AssocRealizations.TypesMeet.NormallyIsomorphic (hlFan n σ) (hlFan n (negSigma σ)) ∧
    (Finset.univ.filter (fun e : Sym2 (Fin (n + 3)) => IsDiagonal e)).image
        (fun e => Finset.Icc 1 (n + 1) \ (hlS n σ e).map Fin.valEmbedding) =
      (Finset.univ.filter (fun e : Sym2 (Fin (n + 3)) => IsDiagonal e)).image
        (fun e => (hlS n (negSigma σ) e).map Fin.valEmbedding) := by sorry

end AssocRealizations.HLClass
