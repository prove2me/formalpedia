-- Prove2me | Theorems.Thm_DepthOneQExp_root_subgroups_kazhdan
-- name    : DepthOneQExp.root_subgroups_kazhdan
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-24T06:55:53.245107+00:00
-- url     : https://prove2.me/theorems/141ee3c8-5cb8-4540-9031-78cdc0aeb2e6
-- title:
--   Root subgroups $X_{12}\cup X_{23}\cup X_{31}$ have relative Kazhdan constant $\ge 1/10$ ($s\ge 3$)
-- statement:
--   Let $s\ge3$ and let $\rho$ be a finite-dimensional unitary representation of $\mathrm{SL}(3s;\mathbb F_2)=\mathrm{EL}(3;\mathrm{Mat}(s;\mathbb F_2))$ with no nonzero invariant vector. Then every unit vector $v$ is moved by at least $1/10$ by some element of one of the three root subgroups
--
--   $$
--   X_{12}=\{E_{1,2}(r)\},\qquad X_{23}=\{E_{2,3}(r)\},\qquad X_{31}=\{E_{3,1}(r)\}\qquad(r\in\mathrm{Mat}(s;\mathbb F_2)).
--   $$
--
--   That is, there are an index pair and an $r$ with $\|\rho(E_{a,b}(r))v-v\|\ge\frac1{10}$.
--
--   Each pair of these subgroups generates a Heisenberg group. For $s\ge3$ the fixed subspaces of the root subgroups are $2^{-s/2}$-orthogonal, and the three-subgroup criterion of Ershov and Jaikin-Zapirain turns this into a uniform relative Kazhdan constant for $X_{12}\cup X_{23}\cup X_{31}$. Combined with relative property (T), this gives the uniform Kazhdan constant of $\Sigma_{3s}$ for $s\ge3$.
--
--   **Formalization Note** Blocks are $0$-based: $X_{12},X_{23},X_{31}$ are `blockElem s 0 1 r`, `blockElem s 1 2 r`, `blockElem s 2 0 r`. The constant $1/10$ is weaker than the $0.349$ obtained from the Ershov–Jaikin-Zapirain bound, which leaves slack.
-- source:
--   M. Ershov, A. Jaikin-Zapirain, Property (T) for noncommutative universal lattices, Invent. Math. 179 (2010), arXiv:0809.4095, Section 2 (almost orthogonal subspaces, Prop. 2.2-2.3, Lemma 2.7) and Section 3 (Prop. 3.2 '3subgps', Cor. 3.3 'T3'); applied to EL_3(Mat(s;F_2)) from arXiv:2609.01605 Fact 2.8

import Mathlib
import Definitions.Def_ConstGapCircuits_spectralGap
import Definitions.Def_DepthOneQExp_blockElem
import Definitions.Def_DepthOneQExp_sigma

namespace DepthOneQExp

/-- Three root subgroups of `EL₃(Mat(s; 𝔽₂))`, `s ≥ 3`, have a uniform relative Kazhdan
constant (Ershov–Jaikin-Zapirain, *Property (T) for noncommutative universal lattices*,
arXiv:0809.4095, Proposition 3.2 and Corollary 3.3, with the Heisenberg orthogonality bound
`2^{-s/2}`): for every unitary representation of `SL(3s; 𝔽₂)` without nonzero invariant vectors
and every unit vector `v`, some element of `X₁₂ ∪ X₂₃ ∪ X₃₁` moves `v` by at least `1/10`.

**Formalization Note** Blocks are 0-based: `X₁₂, X₂₃, X₃₁` are `blockElem s 0 1 r`,
`blockElem s 1 2 r`, `blockElem s 2 0 r`. -/

theorem root_subgroups_kazhdan (s : ℕ) (hs : 3 ≤ s)
    (ρ : ConstGapCircuits.UnitaryRep (Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2)))
    (hρ : ∀ v : EuclideanSpace ℂ (Fin ρ.dim),
      (∀ g, Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v = v) → v = 0)
    (v : EuclideanSpace ℂ (Fin ρ.dim)) (hv : ‖v‖ = 1) :
    ∃ r : Matrix (Fin s) (Fin s) (ZMod 2),
      (1 / 10 : ℝ) ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 0 1 r, det_blockElem s (by decide) r⟩) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v - v‖ ∨
      (1 / 10 : ℝ) ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 1 2 r, det_blockElem s (by decide) r⟩) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v - v‖ ∨
      (1 / 10 : ℝ) ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 2 0 r, det_blockElem s (by decide) r⟩) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v - v‖ := by sorry

end DepthOneQExp
