-- Prove2me | Theorems.Thm_ConeL2G_theorem_1_6
-- name    : ConeL2G.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:42:30.162787+00:00
-- url     : https://prove2.me/theorems/eb2c1815-efa5-41e5-a74f-f74a4f8ca3f8
-- title:
--   Theorem 1.6 (Main Technical Theorem) — the local inequality on cones
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $H=\{v\}\cup H'$ be a cone centered at $v$ with $d=|H'|$ leaves (edges among the leaves are allowed), all of whose degrees are at most $\Delta$, where $\Delta>1$ is an integer (the maximum degree of the ambient graph), and whose color lists satisfy $|L_i|\ge s+\deg_H(i)$ for every vertex $i$, where $s\ge5$ is real. Let $\mu$ be uniform on its proper list colorings, $D_{H'}=\sum_{i\in H'}D_i$ and $\beta_d=1-\big(\frac{s-1}{s}\big)^d$. Then for every $t>0$ and every $f\in L^2(\mu)$
--   $$2\langle D_vf,D_{H'}f\rangle_\mu+t\|D_vf\|_\mu^2+\frac{\beta_d}{t(s-1)}\|D_{H'}f\|_\mu^2+\frac{C\Delta}{ts^3}\langle f,D_{H'}f\rangle_\mu\ \ge\ 0 .$$
--
--   Averaging this inequality over random cones of the graph proves Theorem 1.7.
--
--   Differences from the source:
--   - reading: ∆ the maximum degree (∆ > 1) of the ambient graph G ⊇ H → a natural number Δ with 1 < Δ bounding every degree of H; reason: if H ⊆ G then its degrees are ≤ ∆; conversely a cone with degrees ≤ Δ is a pinned subgraph of G = H ⊔ (a star with Δ leaves), whose maximum degree is Δ, with the same lists; same instances
--   - encoding: O(∆/(ts³)) → C * Δ / (t * s ^ 3) with ∃ C > 0 quantified before the graph, lists, palette, Δ, s, t and f; reason: O(·) denotes an absolute constant
--   - encoding: a subgraph H of G with the lists left after pinning G ∖ H (Section 2.1) → an arbitrary finite graph with arbitrary lists; reason: every finite graph with lists is such a pinned subgraph (take G = H), and every pinned subgraph is a finite graph with lists; same instances
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Theorem 1.6, p.4 (restated p.18)

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_SpinGirth5_heatBath
import Definitions.Def_ConeL2G_unifMass
import Definitions.Def_ConeL2G_beta
import Definitions.Def_ConeL2G_IsCone

open Finset

namespace ConeL2G

/-- **Theorem 1.6 (Main Technical Theorem): the local inequality on cones.** Li–Oveis Gharan,
arXiv:2610.37721, Theorem 1.6, p.4 (restated p.18): "For any `t > 0`, and cone `H = {v} ∪ H′` with
center `v` and leaves `H′` (edges among the leaves are allowed) with `|H′| = d`, suppose `s ⩾ 5` and
`|Lᵢ| ⩾ s + deg_H(i)` for `i ∈ H`. Then we have
`2⟨D_v f, D_{H′}f⟩_µ + t‖D_v f‖²_µ + (β_d/(t(s − 1)))‖D_{H′}f‖²_µ + O(∆/(ts³))⟨f, D_{H′}f⟩_µ ⩾ 0`,
where `D_{H′} = Σ_{i∈H′} Dᵢ` and `β_d = 1 − ((s−1)/s)^d`."

`µ = unifMass H L` (the lists of `H` are those left after pinning `G ∖ H`, Section 1.2 and 2.1),
`D_v = SpinGirth5.singleLap µ v`, `D_{H′} = SpinGirth5.lapSum µ (univ.erase v)`, `d = |V| − 1`.

**Formalization Note.** `∆` is the maximum degree of the ambient graph `G ⊇ H` (`∆ > 1`, p.1), encoded
as a natural number `Δ > 1` bounding every degree of `H`. `O(∆/(ts³))` is `C·Δ/(t·s³)` with an
absolute `C > 0` quantified before the graph, lists, palette, `Δ`, `s`, `t` and `f`. -/
theorem theorem_1_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V)
      [DecidableRel H.Adj] (K : ℕ) (L : V → Finset (Fin K)) (v : V), IsCone H v →
      ∀ (Δ : ℕ) (s t : ℝ), 0 < t → 1 < Δ → (∀ u : V, H.degree u ≤ Δ) → 5 ≤ s →
      (∀ u : V, s + (H.degree u : ℝ) ≤ ((L u).card : ℝ)) →
      ∀ f : (V → Fin K) → ℝ,
        0 ≤ 2 * MarkovMixing.innerPi (unifMass H L) (SpinGirth5.singleLap (unifMass H L) v f)
              (SpinGirth5.lapSum (unifMass H L) (univ.erase v) f) +
            t * MarkovMixing.innerPi (unifMass H L) (SpinGirth5.singleLap (unifMass H L) v f)
              (SpinGirth5.singleLap (unifMass H L) v f) +
            beta s (Fintype.card V - 1) / (t * (s - 1)) *
              MarkovMixing.innerPi (unifMass H L)
                (SpinGirth5.lapSum (unifMass H L) (univ.erase v) f)
                (SpinGirth5.lapSum (unifMass H L) (univ.erase v) f) +
            C * (Δ : ℝ) / (t * s ^ 3) *
              MarkovMixing.innerPi (unifMass H L) f
                (SpinGirth5.lapSum (unifMass H L) (univ.erase v) f) := by sorry

end ConeL2G
