-- Prove2me | Theorems.Thm_AssocRealizations_HLClass_reversal_iso
-- name    : AssocRealizations.HLClass.reversal_iso
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:20:00.058253+00:00
-- url     : https://prove2.me/theorems/8fd6b56f-8d5c-4336-be78-bcdd7df6af93
-- title:
--   Proof of Theorem 4.9, p. 18 — Ass^I_n(σ) and Ass^I_n(σ^t) are normally isomorphic
-- statement:
--   For every $\sigma \in \{+,-\}^{n-1}$:
--
--   1. the normal fans of $\mathrm{Ass}^I_n(\sigma)$ and $\mathrm{Ass}^I_n(\sigma^t)$ are linearly isomorphic;
--   2. with $\tau(i) = n+2-i$, the reversal of the coordinates $1, \dots, n+1$,
--   $$\{S_\delta(\sigma^t) : \delta\} = \{\tau(S_\delta(\sigma)) : \delta\}.$$
--
--   The isomorphism is induced by the permutation $\tau$ of coordinates. This is the reversal half of the "if" direction of Theorem 4.9.
--
--   **Formalization Note** The page writes $\tau(i) = n+1-i$, which maps $1 \mapsto n$ and $n+1 \mapsto 0$; the reversal of $\{1, \dots, n+1\}$ is $\tau(i) = n+2-i$, used here. In the coordinates modulo $e_{[n+1]}$ the induced map is a linear isomorphism (not a coordinate permutation), which is all Definition 2.1 asks.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 18, proof of Theorem 4.9, second paragraph (the printed τ(i) = n + 1 − i read as n + 2 − i)

import Mathlib
import Definitions.Def_AssocRealizations_HLClass_Setting

namespace AssocRealizations.HLClass

open ChvatalArtGallery.FanPartition

/-- Proof of Theorem 4.9 (p. 18): `Ass^I_n(σ)` and `Ass^I_n(σ^t)` are normally isomorphic, and the
family of S-sets of `σ^t` is the image of the family of S-sets of `σ` under
`τ(i) = n + 2 - i`. -/
theorem reversal_iso (n : ℕ) (σ : Fin (n - 1) → Bool) :
    AssocRealizations.TypesMeet.NormallyIsomorphic (hlFan n σ) (hlFan n (revSigma σ)) ∧
    (Finset.univ.filter (fun e : Sym2 (Fin (n + 3)) => IsDiagonal e)).image
        (fun e => ((hlS n σ e).map Fin.valEmbedding).image (fun i => n + 2 - i)) =
      (Finset.univ.filter (fun e : Sym2 (Fin (n + 3)) => IsDiagonal e)).image
        (fun e => (hlS n (revSigma σ) e).map Fin.valEmbedding) := by sorry

end AssocRealizations.HLClass
