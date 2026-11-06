-- Prove2me | Theorems.Thm_ConeL2G_lemma_4_1
-- name    : ConeL2G.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:44:24.365278+00:00
-- url     : https://prove2.me/theorems/1d72a276-81f1-4ef5-b036-65d301501c98
-- title:
--   Lemma 4.1 — $\sum_c\|\sum_i\Pi_{i,c}h\|^2\le(1+\frac1{s-1})\|Dh\|^2+\frac{O(1)}{s^2}\sum_i\deg_H(i)\|D_ih\|^2$
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $H$ be a finite graph with color lists satisfying $\ell_i\ge s+\deg_H(i)$ for every vertex $i$, where $s\ge5$ is real, and let $\mu_H$ be uniform on its proper list colorings. Then for every $h\in L^2(\mu_H)$
--   $$\sum_c\Big\|\sum_{i\in H}\Pi_{i,c}h\Big\|_{\mu_H}^2\ \le\ \Big(1+\frac1{s-1}\Big)\|Dh\|_{\mu_H}^2+\frac{C}{s^2}\sum_{i\in H}\deg_H(i)\,\|D_ih\|_{\mu_H}^2,$$
--   where $D=\sum_{i\in H}D_i$.
--
--   Applied to the leaves of a cone with the center at a dummy color, this bounds the quantity that remains after the center has been removed (Section 6).
--
--   Differences from the source:
--   - encoding: O(1)/s² → C / s ^ 2 with ∃ C > 0 quantified before the graph, the lists, the palette, s and h; reason: O(1) denotes an absolute constant
--   - encoding: Σ_c over colors → Σ over the palette Fin K; reason: Π_{i,c} = 0 for every color outside the lists, so the sums agree
--   - encoding: a subgraph H of G with the lists left after pinning G ∖ H (Section 2.1) → an arbitrary finite graph with arbitrary lists; reason: every finite graph with lists is such a pinned subgraph (take G = H), and every pinned subgraph is a finite graph with lists; same instances
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Lemma 4.1, p.10

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_SpinGirth5_heatBath
import Definitions.Def_ConeL2G_unifMass
import Definitions.Def_ConeL2G_projPi

open Finset

namespace ConeL2G

/-- **Lemma 4.1 (pairwise local inequality).** Li–Oveis Gharan, arXiv:2610.37721, Lemma 4.1,
p.10: "If `ℓᵢ ⩾ s + deg_H(i)` for each `i ∈ H` and `s ⩾ 5`, then for every `h ∈ L²(µ_H)`, we have
`Σ_c ‖Σ_{i∈H} Π_{i,c}h‖²_{µ_H} ⩽ (1 + 1/(s − 1)) ‖Dh‖²_{µ_H} + (O(1)/s²) Σ_{i∈H} deg_H(i) ‖Dᵢh‖²_{µ_H}`."

`H` is an arbitrary finite graph with lists `L` (Section 2.1, p.7: the lists left after pinning),
`µ_H = unifMass H L`, `D = SpinGirth5.lapSum µ_H univ`.

**Formalization Note.** `O(1)` is an absolute constant `C > 0`, quantified before the graph, the
lists, the palette `Fin K`, `s` and `h`; `Σ_c` runs over `Fin K` (`Π_{i,c} = 0` outside the lists). -/
theorem lemma_4_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V)
      [DecidableRel H.Adj] (K : ℕ) (L : V → Finset (Fin K)) (s : ℝ), 5 ≤ s →
      (∀ i : V, s + (H.degree i : ℝ) ≤ ((L i).card : ℝ)) → ∀ h : (V → Fin K) → ℝ,
        ∑ c : Fin K, MarkovMixing.innerPi (unifMass H L) (fun x => ∑ i, projPi H L i c h x)
            (fun x => ∑ i, projPi H L i c h x) ≤
          (1 + 1 / (s - 1)) *
              MarkovMixing.innerPi (unifMass H L) (SpinGirth5.lapSum (unifMass H L) univ h)
                (SpinGirth5.lapSum (unifMass H L) univ h) +
            C / s ^ 2 * ∑ i, (H.degree i : ℝ) *
              MarkovMixing.innerPi (unifMass H L) (SpinGirth5.singleLap (unifMass H L) i h)
                (SpinGirth5.singleLap (unifMass H L) i h) := by sorry

end ConeL2G
