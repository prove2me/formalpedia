-- Prove2me | Theorems.Thm_CodeSW_theorem_16
-- name    : CodeSW.theorem_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:29:23.500272+00:00
-- url     : https://prove2.me/theorems/415ff102-067a-497d-bc8a-7f61167b6259
-- title:
--   Theorem 16 — a flow for $\phi$ with congestion $\rho(F)\le c^22^{2\Delta+5}m^2$
-- statement:
--   **Existence of a good flow for the random cluster model.** Let $0<p<1$. Suppose that $h\in\{0,1\}^{c\times n}$ is $\Delta$-graphic or $\Delta$-cographic, with corresponding edge-vertex incidence matrix $g\in\{0,1\}^{c\times m}$. Then there is a flow $F$ for the random cluster model $\phi$, along paths of the lazy Metropolis chain, with congestion
--   $$\rho(F)\le c^22^{2\Delta+5}m^2.$$
--
--   Combined with Theorem 15, this yields a polynomial mixing bound for the local chain and, through Lemma 9, for the Swendsen-Wang chain.
--
--   Differences from the source:
--   - reading: ρ(F) ≤ O(c²2^{2∆+5}m²) in the statement → ρ(F) ≤ c²2^{2∆+5}m² exactly; reason: the proof ends 'This gives ρ(F) ≤ c²2^{2∆+5}m², as claimed' (p.25), so the explicit bound is the stronger form the page proves
--   - reading: the chain P of the congestion is not named in the theorem → P is the lazy Metropolis chain of p.17; reason: the proof bounds exactly the Metropolis transition probabilities (p.25)
--   - encoding: ∆-graphic / ∆-cographic with coupling g (Definition 10: g the incidence matrix of a graph on m ≤ O(n) vertices; cographic through a column generator h^⊥ of col(h)^⊥) → IsDeltaGraphicVia / IsDeltaCographicVia h g ∆ for the given g, with col(h) in place of ker((h^⊥)ᵀ) and no bound on m; reason: ker((h^⊥)ᵀ) = col(h) for every column generator, and m ≤ O(n) is an asymptotic condition with no content for a single instance, while the bound here is explicit in m
--   - reading: 'edge-vertex incidence matrix of a graph' → every row of g has exactly two ones, in distinct columns (parallel edges allowed, no loops); reason: g has one edge per check with the same row index (p.21), so repeated checks of h force parallel edges; the even-subgraph and worm arguments do not use simplicity
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), Theorem 16, p.19; end of its proof, p.25

import Definitions.Def_CodeSW_metropolis
import Definitions.Def_CodeSW_IsFlow
import Definitions.Def_CodeSW_IsIncidence
open Matrix
open scoped ENNReal

namespace CodeSW

/-- **Theorem 16 (Existence of a good flow for the RC model).** Let `0 < p < 1`. Suppose that
`h ∈ {0,1}^{c×n}` is ∆-graphic or ∆-cographic, with corresponding edge-vertex incidence matrix
`g ∈ {0,1}^{c×m}`. Then there is a flow `F` for the RC model `ϕ` with congestion
`ρ(F) ≤ c² 2^{2∆+5} m²` (Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*,
arXiv:2510.08446, manuscript sha256 4e4abb5e…, Theorem 16, p.19; explicit constant at the end of
its proof, p.25: "This gives ρ(F) ≤ c²2^{2∆+5}m², as claimed").

**Formalization Note** Paths and congestion are taken for the lazy single-check Metropolis chain
of p.17, the chain whose transition probabilities the proof bounds (p.25). The `O(·)` of the
statement is dropped in favour of the explicit constant proved on p.25. -/
theorem theorem_16 {c n m Δ : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2))
    (g : Matrix (Fin c) (Fin m) (ZMod 2)) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hg : IsDeltaGraphicVia h g Δ ∨ IsDeltaCographicVia h g Δ) :
    ∃ F : List (Finset (Fin c)) → ℝ≥0∞, IsFlow (metropolis h p) (rc h p) F ∧
      congestion (metropolis h p) (rc h p) F ≤
        ENNReal.ofReal ((c : ℝ) ^ 2 * 2 ^ (2 * Δ + 5) * (m : ℝ) ^ 2) := by sorry

end CodeSW
