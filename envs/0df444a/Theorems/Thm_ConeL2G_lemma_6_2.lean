-- Prove2me | Theorems.Thm_ConeL2G_lemma_6_2
-- name    : ConeL2G.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:42:30.548227+00:00
-- url     : https://prove2.me/theorems/294b5fab-9702-4f2d-aad4-13f7960968e0
-- title:
--   Lemma 6.2 — $D_{H'}h$ is approximately a leaf function
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $H=\{v\}\cup H'$ be a cone centered at $v$ whose color lists satisfy $\ell_u\ge s+\deg_H(u)$ for every vertex $u$, where $s\ge5$ is real, let $\mu$ be uniform on its proper list colorings, $D_{H'}=\sum_{i\in H'}D_i$ and $d=|H'|$. For every leaf function $h$ there is a leaf function $h'$ such that
--   $$\|h'-D_{H'}h\|_\mu^2\ \le\ \frac{\beta_d}{s-1}\,\|h'\|_\mu^2+\frac{C}{s^3}\sum_{i\in H'}\deg_{H'}(i)\,\|D_ih\|_\mu^2 ,$$
--   where $\deg_{H'}(i)$ is the degree of $i$ among the leaves.
--
--   Even when $h$ does not depend on the center, $D_{H'}h$ may; the lemma says it is close to a function that does not, which is the heart of Proposition 6.1.
--
--   Differences from the source:
--   - encoding: O(1/s³) → C / s ^ 3 with ∃ C > 0 quantified before the graph, the lists, the palette, s and h; reason: O(·) denotes an absolute constant
--   - encoding: leaf function h : Ω_H → ℝ not depending on the center → ConeL2G.IsLeafFn v h on all assignments V → Fin K; reason: every leaf function on Ω_H extends to one that is center-independent everywhere, and off-Ω_H values never enter a µ-weighted form
--   - encoding: deg_{H′}(i), d = |H′| → degree in leafGraph H v, Fintype.card V − 1; reason: same values
--   - encoding: a subgraph H of G with the lists left after pinning G ∖ H (Section 2.1) → an arbitrary finite graph with arbitrary lists; reason: every finite graph with lists is such a pinned subgraph (take G = H), and every pinned subgraph is a finite graph with lists; same instances
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Lemma 6.2, p.20

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_SpinGirth5_heatBath
import Definitions.Def_ConeL2G_unifMass
import Definitions.Def_ConeL2G_beta
import Definitions.Def_ConeL2G_IsCone
import Definitions.Def_ConeL2G_IsLeafFn
import Definitions.Def_ConeL2G_leafGraph

open Finset

namespace ConeL2G

/-- **Lemma 6.2 (`D_{H′}h` is approximately a leaf function).** Li–Oveis Gharan,
arXiv:2610.37721, Lemma 6.2, p.20: "Let `H = {v} ∪ H′` be a cone and the list of colors at every
vertex `u ∈ H` is assumed to satisfy `ℓᵤ ⩾ s + deg_H(u)` and `s ⩾ 5`. For every leaf function `h`,
there exists a leaf function `h′` such that
`‖h′ − D_{H′}h‖²_µ ⩽ (β_d/(s − 1)) ‖h′‖²_µ + O(1/s³) Σ_{i∈H′} deg_{H′}(i) ‖Dᵢh‖²_µ`,
where `d = |H′|`."

`µ = µ_H = unifMass H L`, `D_{H′} = Σ_{i∈H′} Dᵢ = SpinGirth5.lapSum µ (univ.erase v)`,
`deg_{H′}(i)` the degree of `i` among the leaves (in `leafGraph H v`), `d = |V| − 1`.

**Formalization Note.** `O(1/s³)` is `C/s³` with an absolute `C > 0`, quantified before the graph,
the lists, the palette, `s` and `h`. Leaf functions are `ConeL2G.IsLeafFn v` on `V → Fin K`. -/
theorem lemma_6_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V)
      [DecidableRel H.Adj] (K : ℕ) (L : V → Finset (Fin K)) (v : V), IsCone H v →
      ∀ s : ℝ, 5 ≤ s → (∀ u : V, s + (H.degree u : ℝ) ≤ ((L u).card : ℝ)) →
      ∀ h : (V → Fin K) → ℝ, IsLeafFn v h →
        ∃ h' : (V → Fin K) → ℝ, IsLeafFn v h' ∧
          MarkovMixing.innerPi (unifMass H L)
              (fun x => h' x - SpinGirth5.lapSum (unifMass H L) (univ.erase v) h x)
              (fun x => h' x - SpinGirth5.lapSum (unifMass H L) (univ.erase v) h x) ≤
            beta s (Fintype.card V - 1) / (s - 1) * MarkovMixing.innerPi (unifMass H L) h' h' +
              C / s ^ 3 * ∑ i : {u : V // u ≠ v}, ((leafGraph H v).degree i : ℝ) *
                MarkovMixing.innerPi (unifMass H L) (SpinGirth5.singleLap (unifMass H L) i.1 h)
                  (SpinGirth5.singleLap (unifMass H L) i.1 h) := by sorry

end ConeL2G
