-- Prove2me | Theorems.Thm_ConeL2G_claim_6_3
-- name    : ConeL2G.claim_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:42:12.769256+00:00
-- url     : https://prove2.me/theorems/0c33ad87-f4d6-4cde-894c-808945b64698
-- title:
--   Claim 6.3 (corrected: $s>1$) — $\frac{|\Omega_{H'}|}{|\Omega|}\|D^{-v,H'}_ih\|^2_{\mu^{-v}_{H'}}\le\frac1{s-1}\|D_ih\|^2_\mu$
-- statement:
--   Let $H=\{v\}\cup H'$ be a cone centered at $v$ with color lists, $\Omega$ its proper list colorings and $\mu$ uniform on $\Omega$; let $\Omega_{H'}=\{x_{H'}:x\in\Omega\}$ be the restrictions to the leaves, and let $\mu^{-v}_{H'}$ and $D^{-v,H'}_i$ be the uniform law and the single-site Laplacian of the leaves when the center has a dummy color (the induced graph on the leaves with the same lists). Let $s>1$ be real and $\ell_v\ge s+|H'|$. Then for every leaf function $h$ and every leaf $i$
--   $$\frac{|\Omega_{H'}|}{|\Omega|}\,\big\|D^{-v,H'}_ih\big\|^2_{\mu^{-v}_{H'}}\ \le\ \frac1{s-1}\,\|D_ih\|^2_\mu .$$
--
--   The claim compares the leaf Laplacian with and without the center and is used in the proof of Lemma 6.2.
--
--   **Formalization Note** A leaf function is a function $h'$ of the leaf colors, read on $\Omega$ as $x\mapsto h'(x_{H'})$.
--
--   Differences from the source:
--   - correction: no condition on s → 1 < s; reason: false for s < 1: s = 1/2, H the edge v–i, L_v = L_i = {a, b}, h = 1{x_i = a} satisfy every printed assumption (ℓ_v = 2 ≥ s + 1), the left side is 1/4 and the right side 0; at s = 1 the right side is undefined; the paper uses the claim only with s ≥ 5
--   - encoding: leaf function h; µ^{−v}_{H′}, D^{−v,H′}_i (center at a dummy color) → h′ on leaf colorings {u // u ≠ v} → Fin K, read on V → Fin K as h′ ∘ leafRestrict v; unifMass and singleLap of leafGraph H v with lists fun u => L u.1; reason: a dummy center color lies in no leaf list and removes nothing, so the leaves form the induced graph with the same lists; a leaf function is a function of the leaf colors
--   - encoding: |H′|, Ω_{H′} = {x_{H′} : x ∈ Ω} → |V| − 1, (properColorings H L).image (leafRestrict v); reason: same values
--   - encoding: a subgraph H of G with the lists left after pinning G ∖ H (Section 2.1) → an arbitrary finite graph with arbitrary lists; reason: every finite graph with lists is such a pinned subgraph (take G = H), and every pinned subgraph is a finite graph with lists; same instances
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Claim 6.3, p.20

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_SpinGirth5_heatBath
import Definitions.Def_ConeL2G_properColorings
import Definitions.Def_ConeL2G_unifMass
import Definitions.Def_ConeL2G_IsCone
import Definitions.Def_ConeL2G_leafGraph
import Definitions.Def_ConeL2G_leafRestrict

open Finset

namespace ConeL2G

/-- **Claim 6.3 (leaf Laplacian with the center at a dummy color), corrected: `s > 1`.**
Li–Oveis Gharan, arXiv:2610.37721, Claim 6.3, p.20: "If `ℓ_v ⩾ s + |H′|`, then, for every leaf
function `h` and every `i ∈ H′`, we have
`(|Ω_{H′}|/|Ω|) ‖D^{−v,H′}_i h‖²_{µ^{−v}_{H′}} ⩽ (1/(s − 1)) · ‖Dᵢh‖²_µ`."

Setting (Section 6, p.18): `H = {v} ∪ H′` is a cone centered at `v` with arbitrary lists, `Ω = Ω_H`,
`µ = µ_H`, `Dᵢ = D^H_i`; `Ω_{H′} = {x_{H′} : x ∈ Ω}`; `µ^{−v}_{H′}` and `D^{−v,H′}_i` are the uniform law
and the operator of the leaves with the center at a dummy color, i.e. of `leafGraph H v` with the
same lists.

**Correction.** As printed the claim has no condition on `s`, and it fails for `s < 1`
(`s = 1/2`, `H` the edge `v`–`i`, `L_v = L_i = {a, b}`, `h = 1{xᵢ = a}`: left side `1/4`, right side
`0`); at `s = 1` the right side is undefined. The hypothesis `1 < s` is added; the paper uses the
claim with `s ⩾ 5`.

**Formalization Note.** A leaf function is given as `h′` on leaf colorings
`{u // u ≠ v} → Fin K`, identified with `h = h′ ∘ leafRestrict v` on `V → Fin K` (p.18). `|H′|` is
`|V| − 1`. No hypothesis on the leaf lists (the claim has none). -/
theorem claim_6_3 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    {K : ℕ} (L : V → Finset (Fin K)) (v : V) (hcone : IsCone H v) (s : ℝ) (hs : 1 < s)
    (hv : s + ((Fintype.card V : ℝ) - 1) ≤ ((L v).card : ℝ))
    (h' : ({u : V // u ≠ v} → Fin K) → ℝ) (i : V) (hi : i ≠ v) :
    (((properColorings H L).image (leafRestrict v)).card : ℝ) / ((properColorings H L).card : ℝ) *
        MarkovMixing.innerPi (unifMass (leafGraph H v) (fun u => L u.1))
          (SpinGirth5.singleLap (unifMass (leafGraph H v) (fun u => L u.1)) ⟨i, hi⟩ h')
          (SpinGirth5.singleLap (unifMass (leafGraph H v) (fun u => L u.1)) ⟨i, hi⟩ h') ≤
      1 / (s - 1) *
        MarkovMixing.innerPi (unifMass H L)
          (SpinGirth5.singleLap (unifMass H L) i (fun x => h' (leafRestrict v x)))
          (SpinGirth5.singleLap (unifMass H L) i (fun x => h' (leafRestrict v x))) := by sorry

end ConeL2G
