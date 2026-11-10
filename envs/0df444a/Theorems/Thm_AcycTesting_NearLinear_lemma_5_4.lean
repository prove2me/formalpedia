-- Prove2me | Theorems.Thm_AcycTesting_NearLinear_lemma_5_4
-- name    : AcycTesting.NearLinear.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:36:55.996756+00:00
-- url     : https://prove2.me/theorems/1c70c37c-c160-4410-8c1d-36fabb198ce7
-- title:
--   Lemma 5.4 — at most a v/W fraction of the injective embeddings of a v-vertex forest into G◦ meet layer W
-- statement:
--   Let $G^\circ$ be the periodic cover on $\mathbb Z/W\mathbb Z\times X$ of a permutation core $\rho_1,\dots,\rho_{32}$ on $X$, with $W\ge1$. Let $F$ be a coloured forest on $v$ vertices, and let $\mathrm{Emb}_{G^\circ,\mathrm{avoid}}(F)$ count the injective embeddings of $F$ into $G^\circ$ whose images avoid layer $W$ (residue $0$). Then
--   $$\mathrm{Emb}_{G^\circ,\mathrm{avoid}}(F)\ \ge\ \Big(1-\frac vW\Big)\mathrm{Emb}_{G^\circ}(F).\tag{5.3}$$
--   For $v\ge W$ the bound is trivial. Embeddings avoiding the last layer are the ones valid in every YES instance.
--
--   Differences from the source:
--   - encoding: G◦ of §5.1 (base core ρ, layer width W, layer W = residue 0) → coverMaps ρ W for an arbitrary permutation core ρ on a Fintype X and W with [NeZero W]; layer W is (f u).1 = 0; reason: the §5.1 setting; NeZero W is W ≥ 1
--   - encoding: F a colored forest on v vertices → F : ColGraph U with IsColForest F, v = card U; reason: Lean convention
--   - encoding: v/W → real division (card U : ℝ) / W; reason: the source's real ratio
-- source:
--   Czumaj, Peng, Wang, Near-Linear Lower Bounds for Testing Directed Acyclicity, arXiv:2611.04901v1 (sha256 5685fc7b…), p. 19 (PDF 22), Lemma 5.4

import Mathlib
import Definitions.Def_AcycTesting_NearLinear_PermCores
import Definitions.Def_AcycTesting_NearLinear_Forests

namespace AcycTesting.NearLinear

/-- Lemma 5.4 (boundary loss after injectivity): for a coloured forest `F` on `v` vertices,
`Emb_{G◦,avoid}(F) ≥ (1 - v/W) Emb_{G◦}(F)`. -/
theorem lemma_5_4 {U X : Type*} [Fintype U] [Fintype X] (ρ : CoreMaps X) (hρ : IsPermCore ρ)
    (W : ℕ) [NeZero W] (F : ColGraph U) (hF : IsColForest F) :
    (1 - (Fintype.card U : ℝ) / (W : ℝ)) * (Emb (coverMaps ρ W) F : ℝ) ≤
      (EmbAvoid ρ W F : ℝ) := by sorry

end AcycTesting.NearLinear
