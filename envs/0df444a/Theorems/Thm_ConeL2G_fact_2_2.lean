-- Prove2me | Theorems.Thm_ConeL2G_fact_2_2
-- name    : ConeL2G.fact_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:44:02.763993+00:00
-- url     : https://prove2.me/theorems/bc6fa80c-5a75-4df2-9d77-99e9aaf47286
-- title:
--   Fact 2.2 — rank-one decomposition $\sum_{c}\Pi_{i,c}=\big(1+\frac{1}{\ell_i^{-x_{N_H(i)}}-1}\big)D_i$
-- statement:
--   Let $H$ be a finite graph with color lists $(L_i)$, let $\mu=\mu_H$ be uniform on its proper list colorings $\Omega_H$, and let $D_i=I-P_i$ and $\Pi_{i,c}$ be the single-site Laplacian and the rank-one projections onto $e_{i,c}$.
--
--   1. For every vertex $i$, every $h\in L^2(\mu)$ and every $x\in\Omega_H$,
--   $$\sum_{c\in L_i}(\Pi_{i,c}h)(x)=\Big(1+\frac{1}{\ell_i^{-x_{N_H(i)}}-1}\Big)(D_ih)(x).$$
--   2. If $H$ has no edges, then $\ell_i^{-x_{N_H(i)}}=\ell_i$ and, for every $i$, $h$ and $x\in\Omega_H$,
--   $$\sum_{c\in L_i}(\Pi_{i,c}h)(x)=\frac{\ell_i}{\ell_i-1}(D_ih)(x).$$
--
--   This is the "orthonormal" decomposition of $D_i$ into rank-one pieces used throughout Sections 4–6.
--
--   **Formalization Note** Where the printed fraction has denominator $0$ (a single available color) Lean's $x/0=0$ applies; both sides are then $0$.
--
--   Differences from the source:
--   - encoding: any x → x ∈ Ω_H (properColorings H L); reason: the operators act on L²(µ_H); off Ω_H the conditional expectation is a junk value, and the paper's x ranges over Ω_H
--   - encoding: a subgraph H of G with the lists left after pinning G ∖ H (Section 2.1) → an arbitrary finite graph with arbitrary lists; reason: every finite graph with lists is such a pinned subgraph (take G = H), and every pinned subgraph is a finite graph with lists; same instances
--   - encoding: operator identity Σ_{c∈L_i} Π_{i,c} = (ℓ_i/(ℓ_i − 1)) D_i → the identity applied to every h at every x ∈ Ω_H; reason: operators on L²(µ_H) are equal iff they agree on every h at every point of Ω_H
--   - encoding: fraction with denominator ℓ − 1 = 0 (one available color), undefined → Lean's x / 0 = 0; reason: both sides are 0 there (e_{i,c} = 0 and D_i h(x) = 0), so no instance changes
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Fact 2.2, p.8

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_SpinGirth5_heatBath
import Definitions.Def_ConeL2G_properColorings
import Definitions.Def_ConeL2G_unifMass
import Definitions.Def_ConeL2G_avail
import Definitions.Def_ConeL2G_projPi

open Finset

namespace ConeL2G

/-- **Fact 2.2 (rank-one decomposition of `Dᵢ`).** Li–Oveis Gharan, *Local-to-Global Theorems
Based on Cones with Applications to Graph Coloring*, arXiv:2610.37721, Fact 2.2, p.8: "For any
`i`, any `h ∈ L²(µ)`, and any `x`, we have
`Σ_{c∈Lᵢ} (Π_{i,c}h)(x) = (1 + 1/(ℓ_i^{−x_{N_H(i)}} − 1)) (Dᵢh)(x)`.
If `H` is an independent set, `ℓ^{−x_{N_H(i)}} = ℓ_i^H` and we get
`Σ_{c∈Lᵢ} Π_{i,c} = (ℓᵢ/(ℓᵢ − 1)) Dᵢ`."

The graph `H` and its lists are arbitrary (Section 2.1, p.7: the lists left after pinning).
`µ = µ_H = unifMass H L`, `Dᵢ = SpinGirth5.singleLap µ i`.

**Formalization Note.** "Any `x`" is `x ∈ Ω_H`: the operators are defined on `L²(µ_H)`, and off
`Ω_H` the conditional expectation is Lean's junk value. The operator identity of the second
sentence is stated pointwise on `Ω_H`. Where the printed fraction has denominator `0` (one
available color), Lean's `x / 0 = 0` applies; both sides are then `0`. -/
theorem fact_2_2 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    {K : ℕ} (L : V → Finset (Fin K)) :
    (∀ (i : V) (h : (V → Fin K) → ℝ), ∀ x ∈ properColorings H L,
      ∑ c ∈ L i, projPi H L i c h x =
        (1 + 1 / (((avail H L i x).card : ℝ) - 1)) * SpinGirth5.singleLap (unifMass H L) i h x) ∧
    ((∀ i j : V, ¬ H.Adj i j) → ∀ (i : V) (h : (V → Fin K) → ℝ), ∀ x ∈ properColorings H L,
      (avail H L i x).card = (L i).card ∧
      ∑ c ∈ L i, projPi H L i c h x =
        (((L i).card : ℝ) / (((L i).card : ℝ) - 1)) * SpinGirth5.singleLap (unifMass H L) i h x) := by sorry

end ConeL2G
