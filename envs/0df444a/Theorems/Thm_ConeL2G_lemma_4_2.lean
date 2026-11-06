-- Prove2me | Theorems.Thm_ConeL2G_lemma_4_2
-- name    : ConeL2G.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:44:22.511202+00:00
-- url     : https://prove2.me/theorems/383978e5-a67d-4213-aaa0-5713755b5357
-- title:
--   Lemma 4.2 — $\sum_c\langle\Pi_{1,c}f,\Pi_{2,c}f\rangle_\mu\le(1+\frac1{s-1})\langle D_1f,D_2f\rangle_\mu$ for two isolated vertices
-- statement:
--   Let $H$ consist of two isolated vertices $1,2$ with lists $L_1,L_2$ of sizes $\ell_1,\ell_2\ge s$, where $s\ge2$ is real, and let $\mu$ be uniform on $L_1\times L_2$. Then for every $f\in L^2(\mu)$
--   $$\sum_c\langle\Pi_{1,c}f,\Pi_{2,c}f\rangle_\mu\ \le\ \Big(1+\frac1{s-1}\Big)\langle D_1f,D_2f\rangle_\mu .$$
--
--   This is the non-adjacent case of the pairwise inequality of Lemma 4.1.
--
--   Differences from the source:
--   - encoding: vertices 1 and 2 → vertices 0 and 1 of Fin 2; no edge is ⊥, one edge is ⊤; reason: relabelling; same instances
--   - encoding: Σ_c over colors → Σ over the palette Fin K; reason: Π_{i,c} = 0 for every color outside the lists, so the sums agree
--   - encoding: a subgraph H of G with the lists left after pinning G ∖ H (Section 2.1) → an arbitrary finite graph with arbitrary lists; reason: every finite graph with lists is such a pinned subgraph (take G = H), and every pinned subgraph is a finite graph with lists; same instances
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Lemma 4.2, p.11

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_SpinGirth5_heatBath
import Definitions.Def_ConeL2G_unifMass
import Definitions.Def_ConeL2G_projPi

namespace ConeL2G

/-- **Lemma 4.2 (two isolated vertices).** Li–Oveis Gharan, arXiv:2610.37721, Lemma 4.2, p.11:
"Given a graph of two isolated vertices labeled 1 and 2, suppose `s ⩾ 2`, and let `L₁, L₂` be
lists of sizes `ℓ₁, ℓ₂ ⩾ s`. Then for every `f ∈ L²(µ)`, we have
`Σ_c ⟨Π_{1,c}f, Π_{2,c}f⟩_µ ⩽ (1 + 1/(s − 1)) ⟨D₁f, D₂f⟩_µ`."

**Formalization Note.** Vertices 1, 2 are `0, 1 : Fin 2`, the graph is `⊥`; `Σ_c` runs over the
whole palette `Fin K` (`Π_{i,c} = 0` for colors outside the lists). `µ = unifMass ⊥ L`. -/
theorem lemma_4_2 {K : ℕ} (L : Fin 2 → Finset (Fin K)) (s : ℝ) (hs : 2 ≤ s)
    (hL0 : s ≤ ((L 0).card : ℝ)) (hL1 : s ≤ ((L 1).card : ℝ)) (f : (Fin 2 → Fin K) → ℝ) :
    ∑ c : Fin K, MarkovMixing.innerPi (unifMass ⊥ L) (projPi ⊥ L 0 c f) (projPi ⊥ L 1 c f) ≤
      (1 + 1 / (s - 1)) *
        MarkovMixing.innerPi (unifMass ⊥ L) (SpinGirth5.singleLap (unifMass ⊥ L) 0 f)
          (SpinGirth5.singleLap (unifMass ⊥ L) 1 f) := by sorry

end ConeL2G
