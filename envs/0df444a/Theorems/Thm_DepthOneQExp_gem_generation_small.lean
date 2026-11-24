-- Prove2me | Theorems.Thm_DepthOneQExp_gem_generation_small
-- name    : DepthOneQExp.gem_generation_small
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-24T06:55:51.89059+00:00
-- url     : https://prove2.me/theorems/eb014684-a8b4-4540-b781-66f9c1fc0213
-- title:
--   $\mathrm{SL}(3s;\mathbb F_2)$, $s\le 2$, is a product of $19$ generalized elementary matrices
-- statement:
--   Let $s\in\{1,2\}$ and $R=\mathrm{Mat}(s;\mathbb F_2)$. Every $g\in\mathrm{SL}(3s;\mathbb F_2)=\mathrm{EL}(3;R)$ is a product of $19$ generalized elementary matrices. Each factor is of one of the four types
--
--   $$
--   E_{1,3}(r_1)E_{2,3}(r_2),\quad E_{2,1}(r_1)E_{3,1}(r_2),\quad E_{1,2}(r_1)E_{1,3}(r_2),\quad E_{3,1}(r_1)E_{3,2}(r_2)\qquad(r_1,r_2\in R).
--   $$
--
--   Identity factors ($r_1=r_2=0$) are allowed for padding.
--
--   Block row reduction (Kassabov, proof of Theorem 9) uses $7$ left multiplications by GEMs to bring $g$ to $\mathrm{diag}(h,I,I)$ with $h\in\mathrm{GL}_s(\mathbb F_2)$. For $s\le2$, $h$ is a product of at most three transvections, and each costs $4$ GEMs via $\mathrm{diag}(1+ab,1,1)=E_{1,2}(a)E_{2,1}(b)E_{1,2}(a)E_{2,1}(b)$ when $ba=0$. This bounded generation, together with relative property (T), yields the Kazhdan bound for the small cases $s=1,2$, where the Heisenberg orthogonality argument is not strong enough.
--
--   **Formalization Note** Blocks are $0$-based (`blockElem s a b r` is $E_{a+1,b+1}(r)$); the product is `List.prod (List.ofFn h)` of $19$ factors.
-- source:
--   M. Kassabov, Universal lattices and unbounded rank expanders, arXiv:math/0502237, proof of Theorem 9 (Section 4.1: 17-GEM reduction picture; footnote on SL_2(F_2)) and Section 3 identities; applied to SL(3s;F_2)=EL(3;Mat(s;F_2)), Fact 2.8 of arXiv:2609.01605

import Mathlib
import Definitions.Def_ConstGapCircuits_spectralGap
import Definitions.Def_DepthOneQExp_blockElem
import Definitions.Def_DepthOneQExp_sigma

namespace DepthOneQExp

/-- Bounded generation by generalized elementary matrices for `s ≤ 2` (Kassabov,
arXiv:math/0502237, proof of Theorem 9, §4.1: the 7-step block row reduction, completed for
`GL_s(𝔽₂)` with `s ≤ 2` by explicit factorizations): every element of `SL(3s; 𝔽₂)`, `s ∈ {1, 2}`,
is a product of at most `19` GEMs of the four types `E₁₃(r₁)E₂₃(r₂)`, `E₂₁(r₁)E₃₁(r₂)`,
`E₁₂(r₁)E₁₃(r₂)`, `E₃₁(r₁)E₃₂(r₂)` (padding with identities, exactly `19` factors). -/

theorem gem_generation_small (s : ℕ) (hs1 : 1 ≤ s) (hs2 : s ≤ 2)
    (g : Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2)) :
    ∃ h : Fin 19 → Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2),
      (∀ k, ∃ r₁ r₂ : Matrix (Fin s) (Fin s) (ZMod 2),
        h k = (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 0 2 r₁, det_blockElem s (by decide) r₁⟩) * (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 1 2 r₂, det_blockElem s (by decide) r₂⟩) ∨ h k = (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 1 0 r₁, det_blockElem s (by decide) r₁⟩) * (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 2 0 r₂, det_blockElem s (by decide) r₂⟩) ∨
        h k = (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 0 1 r₁, det_blockElem s (by decide) r₁⟩) * (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 0 2 r₂, det_blockElem s (by decide) r₂⟩) ∨ h k = (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 2 0 r₁, det_blockElem s (by decide) r₁⟩) * (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 2 1 r₂, det_blockElem s (by decide) r₂⟩)) ∧
      g = (List.ofFn h).prod := by sorry

end DepthOneQExp
