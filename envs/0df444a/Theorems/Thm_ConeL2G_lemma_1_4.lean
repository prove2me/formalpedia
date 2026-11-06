-- Prove2me | Theorems.Thm_ConeL2G_lemma_1_4
-- name    : ConeL2G.lemma_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:41:37.800394+00:00
-- url     : https://prove2.me/theorems/c9c22be3-0ac6-4f0c-bb88-ba5f66f0b358
-- title:
--   Lemma 1.4 — two-vertex cross term $2\langle D_1f,D_2f\rangle_\mu\ge-\frac1s(\|D_1f\|^2_\mu+\|D_2f\|^2_\mu)$
-- statement:
--   Consider a graph $H$ on two vertices $1,2$ with color lists $L_1,L_2$, and let $\mu$ be uniform on its proper list colorings.
--
--   1. If $H$ has no edges, then for every $f\in L^2(\mu)$, $\langle D_1f,D_2f\rangle_\mu\ge0$.
--   2. If $H$ has the edge $12$, $s\ge5$ is real and $|L_1|,|L_2|\ge s+1$, then for every $f\in L^2(\mu)$
--   $$2\langle D_1f,D_2f\rangle_\mu\ \ge\ -\frac1s\big(\|D_1f\|_\mu^2+\|D_2f\|_\mu^2\big).$$
--
--   Summed over the edges of a graph this already gives a spectral gap of order $1/(\Delta n)$ when every list has more than $2\Delta+2$ colors; it is also the bound used for adjacent pairs in Lemma 4.1.
--
--   Differences from the source:
--   - encoding: vertices 1 and 2 → vertices 0 and 1 of Fin 2; no edge is ⊥, one edge is ⊤; reason: relabelling; same instances
--   - encoding: a subgraph H of G with the lists left after pinning G ∖ H (Section 2.1) → an arbitrary finite graph with arbitrary lists; reason: every finite graph with lists is such a pinned subgraph (take G = H), and every pinned subgraph is a finite graph with lists; same instances
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Lemma 1.4, p.3

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_SpinGirth5_heatBath
import Definitions.Def_ConeL2G_unifMass

namespace ConeL2G

/-- **Lemma 1.4 (two-vertex cross term).** Li–Oveis Gharan, arXiv:2610.37721, Lemma 1.4, p.3:
"Given a graph `H` with vertices 1 and 2. If `H` has no edges then `⟨D₁f, D₂f⟩_µ ⩾ 0`.
Otherwise, suppose `s ⩾ 5` and `|L₁|, |L₂| ⩾ s + 1`. Then for every `f ∈ L²(µ)`, we have
`2⟨D₁f, D₂f⟩_µ ⩾ −(1/s)(‖D₁f‖²_µ + ‖D₂f‖²_µ)`."

**Formalization Note.** The two vertices 1, 2 are `0, 1 : Fin 2`; the graph without edges is `⊥`,
the graph with the edge is `⊤`. The lists `L` are arbitrary (the lists left after pinning,
Section 2.1). `µ = unifMass H L`, `Dᵢ = SpinGirth5.singleLap µ i`, `⟨·,·⟩_µ = MarkovMixing.innerPi µ`,
`‖g‖²_µ = ⟨g, g⟩_µ`; `s` is real. -/
theorem lemma_1_4 {K : ℕ} (L : Fin 2 → Finset (Fin K)) :
    (∀ f : (Fin 2 → Fin K) → ℝ,
      0 ≤ MarkovMixing.innerPi (unifMass ⊥ L) (SpinGirth5.singleLap (unifMass ⊥ L) 0 f)
        (SpinGirth5.singleLap (unifMass ⊥ L) 1 f)) ∧
    (∀ s : ℝ, 5 ≤ s → s + 1 ≤ ((L 0).card : ℝ) → s + 1 ≤ ((L 1).card : ℝ) →
      ∀ f : (Fin 2 → Fin K) → ℝ,
        -(1 / s) * (MarkovMixing.innerPi (unifMass ⊤ L) (SpinGirth5.singleLap (unifMass ⊤ L) 0 f)
              (SpinGirth5.singleLap (unifMass ⊤ L) 0 f) +
            MarkovMixing.innerPi (unifMass ⊤ L) (SpinGirth5.singleLap (unifMass ⊤ L) 1 f)
              (SpinGirth5.singleLap (unifMass ⊤ L) 1 f)) ≤
          2 * MarkovMixing.innerPi (unifMass ⊤ L) (SpinGirth5.singleLap (unifMass ⊤ L) 0 f)
            (SpinGirth5.singleLap (unifMass ⊤ L) 1 f)) := by sorry

end ConeL2G
