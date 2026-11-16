-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_Supplement_lemma_7_1
-- name    : BourgainUnion.Euclidean.Supplement.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:38:27.541265+00:00
-- url     : https://prove2.me/theorems/4cde23db-17c6-4b9e-8747-0ffb39133aea
-- title:
--   Lemma 7.1 — eliminating a set that embeds with distortion $c$
-- statement:
--   Let $Y=A\sqcup B$ be a finite pseudometric space with $A\ne\varnothing$, where $B$ embeds into $\ell_2$ with distortion $c\ge1$: some map $z:B\to\ell_2$ has $d(b,b')\le\|z_b-z_{b'}\|\le c\,d(b,b')$. Let $G$ be a weighted graph on $Y$ (nonnegative symmetric weights, zero diagonal), $G_A$ its canonical sparsifier on $A$ (Lemma 4.4), and as in Lemma 4.6 let $I=E_{G[B]}(d^2)$ be the internal energy of $B$ and $J=\sum_{a\in A,b\in B}g_{ab}d(a,b)^2$ its crossing energy. Then
--   $$E_{G_A}(d^2)\le E_G(d^2)+(c^2-1)I+J+c\sqrt{2\pi IJ}. \tag{23}$$
--   For $c=1$ this is Lemma 4.6.
--
--   Differences from the source:
--   - encoding: Y = A ⊔ B finite → a Fintype pseudometric space, a Finset A and B = univ \ A; reason: as in the published Lemma 4.6
--   - encoding: B embeds into ℓ2 with distortion c ≥ 1 → the published Embeds c on the subspace B, with no separate hypothesis c ≥ 1; reason: Embeds c includes 1 ≤ c, so a separate hypothesis would be redundant
--   - encoding: weighted graphs with g_xy = g_yx ≥ 0, g_xx = 0, and sums over unordered pairs x < y → the published ClusterDecomp.WGraph with the base Loopless predicate; energy = half the ordered-pair sum; reason: symmetry and the zero diagonal make the two sums equal
--   - encoding: real ℓ₂ → square-summable real sequences H2 = lp (fun _ : ℕ => ℝ) 2; reason: H2 is real ℓ₂, the published target of the base mission
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 27, §7, Lemma 7.1, equation (23)

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_EmbeddingModel
import Definitions.Def_BourgainUnion_Euclidean_GraphModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean.Supplement

open BourgainUnion.Euclidean

/-- Lemma 7.1, equation (23), p. 27: `B = Y ∖ A` embeds with distortion `c` (which includes `c ≥ 1`); `I`, `J` are the
internal and crossing energies of `B` as in the published Lemma 4.6. -/
theorem lemma_7_1 {X : Type*} [Fintype X] [DecidableEq X] [PseudoMetricSpace X]
    (A : Finset X) (hA : A.Nonempty) (c : ℝ)
    (hB : Embeds (X := ((↑(Finset.univ \ A) : Set X))) c)
    (G : ClusterDecomp.WGraph X) (hG : Loopless G) :
    energy (canonical G.w A) dist A ≤ energy G.w dist Finset.univ +
      (c^2 - 1) * energy G.w dist (Finset.univ \ A) +
      crossing G.w dist A (Finset.univ \ A) +
      c * Real.sqrt (2*Real.pi*energy G.w dist (Finset.univ \ A)*
        crossing G.w dist A (Finset.univ \ A)) := by sorry

end BourgainUnion.Euclidean.Supplement
