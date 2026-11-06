-- Prove2me | Theorems.Thm_ConeL2G_lemma_4_3
-- name    : ConeL2G.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:44:18.403053+00:00
-- url     : https://prove2.me/theorems/cff4bbc7-5c68-461f-bbc5-0503fa6ec5fb
-- title:
--   Lemma 4.3 — $\sum_c\langle\Pi_{1,c}f,\Pi_{2,c}f\rangle_\mu\le\langle D_1f,D_2f\rangle_\mu+\frac{O(1)}{s^2}(\|D_1f\|^2_\mu+\|D_2f\|^2_\mu)$ on an edge
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $H$ be a single edge between vertices $1$ and $2$ with color lists $L_1,L_2$ of sizes $\ell_1,\ell_2\ge s+1$, where $s\ge5$ is real, and let $\mu$ be uniform on its proper list colorings. Then for every $f\in L^2(\mu)$
--   $$\sum_c\langle\Pi_{1,c}f,\Pi_{2,c}f\rangle_\mu\ \le\ \langle D_1f,D_2f\rangle_\mu+\frac{C}{s^2}\big(\|D_1f\|_\mu^2+\|D_2f\|_\mu^2\big).$$
--
--   This is the adjacent case of the pairwise inequality of Lemma 4.1 and the technical core of Section 4.
--
--   Differences from the source:
--   - encoding: O(1)/s² → C / s ^ 2 with ∃ C > 0 quantified before the palette, the lists, s and f; reason: O(1) denotes an absolute constant
--   - encoding: vertices 1 and 2 → vertices 0 and 1 of Fin 2; no edge is ⊥, one edge is ⊤; reason: relabelling; same instances
--   - encoding: Σ_c over colors → Σ over the palette Fin K; reason: Π_{i,c} = 0 for every color outside the lists, so the sums agree
--   - encoding: a subgraph H of G with the lists left after pinning G ∖ H (Section 2.1) → an arbitrary finite graph with arbitrary lists; reason: every finite graph with lists is such a pinned subgraph (take G = H), and every pinned subgraph is a finite graph with lists; same instances
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Lemma 4.3, p.11

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_SpinGirth5_heatBath
import Definitions.Def_ConeL2G_unifMass
import Definitions.Def_ConeL2G_projPi

namespace ConeL2G

/-- **Lemma 4.3 (the edge cross term).** Li–Oveis Gharan, arXiv:2610.37721, Lemma 4.3, p.11:
"Given a graph consisting of an edge between vertices 1 and 2. Suppose `s ⩾ 5`, and let `L₁, L₂` be
lists of sizes `ℓ₁, ℓ₂ ⩾ s + 1`. Then for every `f ∈ L²(µ)`, we have
`Σ_c ⟨Π_{1,c}f, Π_{2,c}f⟩_µ ⩽ ⟨D₁f, D₂f⟩_µ + (O(1)/s²)(‖D₁f‖²_µ + ‖D₂f‖²_µ)`."

**Formalization Note.** `O(1)` is an absolute constant `C > 0`, quantified before the palette, the
lists, `s` and `f`. Vertices 1, 2 are `0, 1 : Fin 2`, the graph is `⊤`, `µ = unifMass ⊤ L`; `Σ_c`
runs over the palette `Fin K`. -/
theorem lemma_4_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (L : Fin 2 → Finset (Fin K)) (s : ℝ), 5 ≤ s →
      s + 1 ≤ ((L 0).card : ℝ) → s + 1 ≤ ((L 1).card : ℝ) → ∀ f : (Fin 2 → Fin K) → ℝ,
        ∑ c : Fin K, MarkovMixing.innerPi (unifMass ⊤ L) (projPi ⊤ L 0 c f) (projPi ⊤ L 1 c f) ≤
          MarkovMixing.innerPi (unifMass ⊤ L) (SpinGirth5.singleLap (unifMass ⊤ L) 0 f)
              (SpinGirth5.singleLap (unifMass ⊤ L) 1 f) +
            C / s ^ 2 *
              (MarkovMixing.innerPi (unifMass ⊤ L) (SpinGirth5.singleLap (unifMass ⊤ L) 0 f)
                  (SpinGirth5.singleLap (unifMass ⊤ L) 0 f) +
                MarkovMixing.innerPi (unifMass ⊤ L) (SpinGirth5.singleLap (unifMass ⊤ L) 1 f)
                  (SpinGirth5.singleLap (unifMass ⊤ L) 1 f)) := by sorry

end ConeL2G
