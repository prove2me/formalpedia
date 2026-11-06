-- Prove2me | Theorems.Thm_ConeL2G_proposition_6_1
-- name    : ConeL2G.proposition_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:42:25.311167+00:00
-- url     : https://prove2.me/theorems/268b44ac-f681-4414-87e9-3f43cfa8670b
-- title:
--   Proposition 6.1 — $(1-\frac{\beta_d}{s-1})\|D_vD_{H'}h\|^2_\mu\le\frac{\beta_d}{s-1}\|P_vD_{H'}h\|^2_\mu+O(\frac{\Delta}{s^3})\langle h,D_{H'}h\rangle_\mu$
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $H=\{v\}\cup H'$ be a cone centered at $v$, all of whose degrees are at most $\Delta$, where $\Delta>1$ is an integer (the maximum degree of the ambient graph), and whose color lists satisfy $\ell_u\ge s+\deg_H(u)$ for every vertex $u$, where $s\ge5$ is real. Let $\mu$ be uniform on its proper list colorings, $D_{H'}=\sum_{i\in H'}D_i$ and $d=|H'|$. For every leaf function $h$
--   $$\Big(1-\frac{\beta_d}{s-1}\Big)\|D_vD_{H'}h\|_\mu^2\ \le\ \frac{\beta_d}{s-1}\,\|P_vD_{H'}h\|_\mu^2+\frac{C\Delta}{s^3}\,\langle h,D_{H'}h\rangle_\mu .$$
--
--   The proposition bounds the dependence of $D_{H'}h$ on the center color; it is the main input of Theorem 1.6.
--
--   Differences from the source:
--   - reading: ∆ the maximum degree (∆ > 1) of the ambient graph G ⊇ H → a natural number Δ with 1 < Δ bounding every degree of H; reason: if H ⊆ G then its degrees are ≤ ∆; conversely a cone with degrees ≤ Δ is a pinned subgraph of G = H ⊔ (a star with Δ leaves), whose maximum degree is Δ, with the same lists; same instances
--   - encoding: O(∆/s³) → C * Δ / s ^ 3 with ∃ C > 0 quantified before everything else; reason: O(·) denotes an absolute constant
--   - encoding: leaf function h : Ω_H → ℝ not depending on the center → ConeL2G.IsLeafFn v h on all assignments V → Fin K; reason: every leaf function on Ω_H extends to one that is center-independent everywhere, and off-Ω_H values never enter a µ-weighted form
--   - encoding: a subgraph H of G with the lists left after pinning G ∖ H (Section 2.1) → an arbitrary finite graph with arbitrary lists; reason: every finite graph with lists is such a pinned subgraph (take G = H), and every pinned subgraph is a finite graph with lists; same instances
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Proposition 6.1, p.19

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_SpinGirth5_heatBath
import Definitions.Def_ConeL2G_unifMass
import Definitions.Def_ConeL2G_beta
import Definitions.Def_ConeL2G_IsCone
import Definitions.Def_ConeL2G_IsLeafFn

open Finset

namespace ConeL2G

/-- **Proposition 6.1 (`D_v D_{H′}` on leaf functions).** Li–Oveis Gharan, arXiv:2610.37721,
Proposition 6.1, p.19: "Let `H = {v} ∪ H′` be a cone, and suppose that the list of colors at every
vertex `u ∈ H` satisfies `ℓᵤ ⩾ s + deg_H(u)` and `s ⩾ 5`. For every leaf function `h`, we have
`(1 − β_d/(s − 1)) ‖D_v D_{H′}h‖²_µ ⩽ (β_d/(s − 1)) ‖P_v D_{H′}h‖²_µ + O(∆/s³) ⟨h, D_{H′}h⟩_µ`,
where `d = |H′|`."

`µ = unifMass H L`, `P_v = SpinGirth5.heatBath µ v`, `D_v = SpinGirth5.singleLap µ v`,
`D_{H′} = SpinGirth5.lapSum µ (univ.erase v)`, `d = |V| − 1`.

**Formalization Note.** `∆` is the maximum degree of the ambient graph `G ⊇ H` (`∆ > 1`, p.1); it is
encoded as a natural number `Δ > 1` bounding every degree of `H`. `O(∆/s³)` is `C·Δ/s³` with an
absolute `C > 0` quantified before everything else. -/
theorem proposition_6_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V)
      [DecidableRel H.Adj] (K : ℕ) (L : V → Finset (Fin K)) (v : V), IsCone H v →
      ∀ (Δ : ℕ) (s : ℝ), 1 < Δ → (∀ u : V, H.degree u ≤ Δ) → 5 ≤ s →
      (∀ u : V, s + (H.degree u : ℝ) ≤ ((L u).card : ℝ)) →
      ∀ h : (V → Fin K) → ℝ, IsLeafFn v h →
        (1 - beta s (Fintype.card V - 1) / (s - 1)) *
            MarkovMixing.innerPi (unifMass H L)
              (SpinGirth5.singleLap (unifMass H L) v
                (SpinGirth5.lapSum (unifMass H L) (univ.erase v) h))
              (SpinGirth5.singleLap (unifMass H L) v
                (SpinGirth5.lapSum (unifMass H L) (univ.erase v) h)) ≤
          beta s (Fintype.card V - 1) / (s - 1) *
              MarkovMixing.innerPi (unifMass H L)
                (SpinGirth5.heatBath (unifMass H L) v
                  (SpinGirth5.lapSum (unifMass H L) (univ.erase v) h))
                (SpinGirth5.heatBath (unifMass H L) v
                  (SpinGirth5.lapSum (unifMass H L) (univ.erase v) h)) +
            C * (Δ : ℝ) / s ^ 3 *
              MarkovMixing.innerPi (unifMass H L) h
                (SpinGirth5.lapSum (unifMass H L) (univ.erase v) h) := by sorry

end ConeL2G
