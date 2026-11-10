-- Prove2me | Theorems.Thm_AcycTesting_NearLinear_lemma_5_3
-- name    : AcycTesting.NearLinear.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:36:34.595794+00:00
-- url     : https://prove2.me/theorems/2241e223-bcd9-4c52-aa83-9d13a7ae7218
-- title:
--   Lemma 5.3 — the periodic cover of a base core keeps weak girth > γ and has the layer translation as automorphism
-- statement:
--   Let $G_{\mathrm{base}}$ be a permutation core on a set $X$ of $T$ vertices with bijections $\rho_1,\dots,\rho_{32}$ and weak girth greater than $\gamma$, and let $W\ge1$. Let $G^\circ$ be the core on $\mathbb Z/W\mathbb Z\times X$ with
--   $$P_a(i,x)=(i+1,\rho_a(x)),\qquad a\in[32].$$
--   Then every $P_a$ is a bijection, $G^\circ$ has $TW$ vertices, $G^\circ$ has weak girth greater than $\gamma$, and the layer translation $\tau(i,x)=(i+1,x)$ is a bijection with $P_a\circ\tau=\tau\circ P_a$ for every colour $a$ (a colour-preserving automorphism). The periodic cover is the comparison core for the acyclic YES instances.
--
--   Differences from the source:
--   - encoding: Z/WZ with W ≥ 1 → ZMod W with [NeZero W]; reason: NeZero W is W ≥ 1
--   - encoding: G◦ is a permutation core on TW vertices → each coverMaps ρ W a is bijective and card (ZMod W × X) = T·W; reason: the two parts of "permutation core on TW vertices"
--   - encoding: (i, x) ↦ (i + 1, x) is a color-preserving automorphism → layerShift is bijective and commutes with every colour map; reason: an automorphism of a core is a bijection commuting with every P_a, which preserves direction and colour of every occurrence
--   - encoding: base core on T vertices → a Fintype X with card X = T and bijective ρ a; reason: Lean convention
-- source:
--   Czumaj, Peng, Wang, Near-Linear Lower Bounds for Testing Directed Acyclicity, arXiv:2611.04901v1 (sha256 5685fc7b…), p. 18 (PDF 21), Lemma 5.3

import Mathlib
import Definitions.Def_AcycTesting_NearLinear_PermCores
import Definitions.Def_AcycTesting_NearLinear_Forests

namespace AcycTesting.NearLinear

/-- Lemma 5.3 (periodic cover). -/
theorem lemma_5_3 {X : Type*} [Fintype X] (ρ : CoreMaps X) (hρ : IsPermCore ρ) (T : ℕ)
    (hT : Fintype.card X = T) (γ : ℕ) (hgirth : CoreGirthGT ρ γ) (W : ℕ) [NeZero W] :
    IsPermCore (coverMaps ρ W) ∧
      Fintype.card (ZMod W × X) = T * W ∧
      CoreGirthGT (coverMaps ρ W) γ ∧
      Function.Bijective (layerShift (X := X) W) ∧
      ∀ (a : Fin 32) (y : ZMod W × X),
        coverMaps ρ W a (layerShift W y) = layerShift W (coverMaps ρ W a y) := by sorry

end AcycTesting.NearLinear
