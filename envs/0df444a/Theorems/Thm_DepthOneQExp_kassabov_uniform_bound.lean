-- Prove2me | Theorems.Thm_DepthOneQExp_kassabov_uniform_bound
-- name    : DepthOneQExp.kassabov_uniform_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-24T06:51:36.476507+00:00
-- url     : https://prove2.me/theorems/e9da374b-f352-4b39-835a-60088b8d21b4
-- title:
--   Kassabov's uniform bound: some generator of $\Sigma_{3s}$ moves every unit vector by $\ge 1/250$
-- statement:
--   Let $s\ge1$ and let $\Sigma_{3s}=\{\sigma_1,\dots,\sigma_{14}\}\subset\mathrm{SL}(3s;\mathbb F_2)=\mathrm{EL}(3;\mathrm{Mat}(s;\mathbb F_2))$ be Kassabov's generating family: the elementary block matrices $E_{a,b}(I_s)$ for $a\ne b$ and $E_{a,b}(A)$, $E_{a,b}(B)$ for $|a-b|=1$, where $A$ is the cyclic shift and $B=e_1e_1^{\mathsf T}$. Let $\rho$ be a finite-dimensional unitary representation of $\mathrm{SL}(3s;\mathbb F_2)$ with no nonzero invariant vector. Then every unit vector $v$ satisfies
--
--   $$
--   \max_{1\le i\le14}\|\rho(\sigma_i)v-v\|\ \ge\ \frac1{250}.
--   $$
--
--   Equivalently, the Kazhdan constant satisfies $K(\mathrm{SL}(3s;\mathbb F_2);\Sigma_{3s})\ge\frac1{250}>\frac1{400}$ uniformly in $s$. This is Kassabov's bounded-Kazhdan-constant theorem for $\mathrm{SL}(3s;\mathbb F_2)$ (Theorem 2.11 of the paper), stated pointwise; it is the only source of uniformity in $s$ for the depth-1 expanders.
--
--   **Formalization Note** The statement quantifies over `ConstGapCircuits.UnitaryRep` (continuous finite-dimensional unitary matrix representations; the group carries the discrete topology). The constant $1/250$ is chosen to exceed Kassabov's $1/400$; taking the infimum over representations and unit vectors gives the milestone `theorem_2_11`.
-- source:
--   M. Kassabov, Universal lattices and unbounded rank expanders, Invent. Math. 170 (2007) 297-326, arXiv:math/0502237, Theorem 9 (published Theorem 8a; proof in Section 4.1, using Theorem 2.2/Corollary 2.8); quoted as Theorem 2.11 (Eq. 2.20) in Anshu-Balasubramanian-Haferkamp-Harrow-Tan, arXiv:2609.01605, p.10

import Mathlib
import Definitions.Def_ConstGapCircuits_spectralGap
import Definitions.Def_DepthOneQExp_sigma

namespace DepthOneQExp

/-- Kassabov's uniform Kazhdan bound for `Σ_{3s}` in pointwise form (Kassabov, *Universal lattices
and unbounded rank expanders*, Invent. Math. 170 (2007), arXiv:math/0502237, Theorem 9 = [Kas07b,
Theorem 8a] as quoted in Theorem 2.11 of arXiv:2609.01605): for every `s ≥ 1`, every
finite-dimensional unitary representation of `SL(3s; 𝔽₂)` without nonzero invariant vectors and
every unit vector `v`, some generator in `Σ_{3s}` moves `v` by at least `1/250`.

**Formalization Note** The constant `1/250 > 1/400` is uniform in `s`; taking the infimum gives
Theorem 2.11. Representations are `ConstGapCircuits.UnitaryRep`; `Σ_{3s}` is the indexed family
`sigma s`. -/
theorem kassabov_uniform_bound (s : ℕ) (hs : 1 ≤ s)
    (ρ : ConstGapCircuits.UnitaryRep (Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2)))
    (hρ : ∀ v : EuclideanSpace ℂ (Fin ρ.dim),
      (∀ g, Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v = v) → v = 0)
    (v : EuclideanSpace ℂ (Fin ρ.dim)) (hv : ‖v‖ = 1) :
    (1 / 250 : ℝ) ≤ ⨆ i : Fin 14, ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
      (ρ.hom (sigma s i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v - v‖ := by sorry

end DepthOneQExp
