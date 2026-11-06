-- Prove2me | Theorems.Thm_ConeL2G_claim_4_5
-- name    : ConeL2G.claim_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:41:51.020339+00:00
-- url     : https://prove2.me/theorems/c1872ffc-05e5-4375-9a9a-fddec186c93a
-- title:
--   Claim 4.5 — $\langle g_1,g_2\rangle_\mu=-\frac1{|\Omega|}\sum_{c\in L_1\cap L_2}g_1(c)g_2(c)$ on an edge
-- statement:
--   Let $H$ be a single edge between vertices $1$ and $2$ with color lists $L_1,L_2$, let $\Omega$ be its proper list colorings and $\mu$ the uniform distribution on $\Omega$. Let $g_1$ be a function of $x_1$ only and $g_2$ a function of $x_2$ only, and suppose that
--   $$\sum_{c\in L_1}g_1(c)=0\qquad\text{or}\qquad\sum_{c\in L_2}g_2(c)=0 .$$
--   Then
--   $$\langle g_1,g_2\rangle_\mu=-\frac1{|\Omega|}\sum_{c\in L_1\cap L_2}g_1(c)\,g_2(c).$$
--
--   The identity is used in the proof of Lemma 4.3 to evaluate inner products of the degree-one parts of a function on an edge.
--
--   Differences from the source:
--   - generalization: the edge of Lemma 4.3, with s ≥ 5 and ℓ₁, ℓ₂ ≥ s + 1 (the claim is stated inside that proof) → an edge with arbitrary lists; reason: the identity is pure counting and holds for any lists; it specializes to the lists of Lemma 4.3
--   - encoding: g₁ ∈ L²(µ) a function of x₁ only (or g₁ ∈ ℝ^{L₁} extended), and likewise g₂ → x ↦ g₁ (x 0) and x ↦ g₂ (x 1) with g₁, g₂ : Fin K → ℝ; the two alternative hypotheses as one disjunction; reason: every function of x₁ on Ω has this form, and the claim's three sentences are exactly the two hypotheses and this extension
--   - encoding: vertices 1 and 2 → vertices 0 and 1 of Fin 2; no edge is ⊥, one edge is ⊤; reason: relabelling; same instances
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Claim 4.5, p.15

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_ConeL2G_properColorings
import Definitions.Def_ConeL2G_unifMass

namespace ConeL2G

/-- **Claim 4.5 (inner product of single-coordinate functions on an edge).** Li–Oveis Gharan,
arXiv:2610.37721, Claim 4.5, p.15: "Let `g₁, g₂ ∈ L²(µ)` such that `g₁` is function of only `x₁` and
`g₂` a function of only `x₂` be such that `Σ_{c∈L₁} g₁(c, ·) = 0`. Then
`⟨g₁, g₂⟩_µ = −(1/|Ω|) Σ_{c∈L₁∩L₂} g₁(c, ·) g₂(·, c)`. The same conclusion would also hold if we
instead only had `Σ_{c∈L₂} g₂(·, c) = 0`. Furthermore, the same conclusion holds even if
`g₁ ∈ ℝ^{L₁}` (or `g₂ ∈ ℝ^{L₂}`) simply by extending `g₁(x₁, x₂) = g₁(x₁)` for any `(x₁, x₂) ∈ Ω`."

The setting is the graph of Lemma 4.3: one edge between vertices 1 and 2 (`⊤` on `Fin 2`), `Ω` its
proper list colorings, `µ` uniform on `Ω`.

**Formalization Note.** A function of `x₁` only is `x ↦ g₁ (x 0)` with `g₁ : Fin K → ℝ` (this is also
the "Furthermore" extension); the disjunction covers both the main hypothesis and the alternative
one. The lists are arbitrary (the identity is pure counting); if `Ω = ∅` both sides are `0`. -/
theorem claim_4_5 {K : ℕ} (L : Fin 2 → Finset (Fin K)) (g₁ g₂ : Fin K → ℝ)
    (hsum : ∑ c ∈ L 0, g₁ c = 0 ∨ ∑ c ∈ L 1, g₂ c = 0) :
    MarkovMixing.innerPi (unifMass ⊤ L) (fun x => g₁ (x 0)) (fun x => g₂ (x 1)) =
      -(1 / ((properColorings ⊤ L).card : ℝ)) * ∑ c ∈ L 0 ∩ L 1, g₁ c * g₂ c := by sorry

end ConeL2G
