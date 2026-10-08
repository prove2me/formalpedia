-- Prove2me | Theorems.Thm_AffinePSD_Necessity_lemma_4_17
-- name    : AffinePSD.Necessity.lemma_4_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:36.221088+00:00
-- url     : https://prove2.me/theorems/0ec0c586-15f0-44d3-a057-04f9b86b6c12
-- title:
--   Lemma 4.17 — first and second partial derivatives of $\det$ at a diagonal $y\in S_d^+$
-- statement:
--   Let $y \in S_d^+$ be diagonal, $y = \mathrm{diag}(y_{11}, \dots, y_{dd})$, and regard $\det$ as a function of all $d^2$ entries $x_{ij}$ of $x \in M_d$. Then
--   $$\frac{\partial \det(x)}{\partial x_{ij}}\Big|_{x=y} = \begin{cases} \prod_{k \ne i} y_{kk}, & i = j,\\ 0, & \text{else,}\end{cases}$$
--   and
--   $$\frac{\partial^2 \det(x)}{\partial x_{ij}\,\partial x_{ji}}\Big|_{x=y} = -\prod_{k=1,\,k\ne i,\,k \ne j}^d y_{kk} \quad (1 \le i < j \le d), \qquad \frac{\partial^2\det(x)}{\partial x_{ij}^2}\Big|_{x=y} = 0 \quad (1 \le i \le j \le d),$$
--   where the empty product is $1$.
--
--   These derivatives evaluate the condition (4.20) at diagonal boundary points in the proof of the drift condition (2.4) (Proposition 4.18).
--
--   **Formalization Note.** $\partial/\partial x_{ij}$ is the derivative of $x \mapsto \det x$ on $M_d$ in the direction of the unit matrix $E^{ij}$, as in the proof, which differentiates Leibniz's formula (4.22) entrywise. The symmetrized directions used for the generator are not used here; with them the mixed derivative would be $-\tfrac12\prod$ instead.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Lemma 4.17, pp. 35–36

import Mathlib
import Definitions.Def_AffinePSD_Necessity_Cone

namespace AffinePSD.Necessity

/-- Lemma 4.17 (arXiv:0910.0137v3, §4.4, pp. 35–36). Let `y ∈ S_d^+` be diagonal,
`y = diag(y_{11}, …, y_{dd})`. Then
`∂det(x)/∂x_{ij}|_{x=y} = ∏_{k≠i} y_{kk}` if `i = j` and `0` otherwise;
`∂²det(x)/∂x_{ij}∂x_{ji}|_{x=y} = −∏_{k≠i,j} y_{kk}` for `1 ≤ i < j ≤ d`;
`∂²det(x)/∂x_{ij}²|_{x=y} = 0` for `1 ≤ i ≤ j ≤ d`; the empty product is `1`.

**Formalization Note.** Raw entry derivatives: `det` is the function `x ↦ det x` on all of `M_d`, and
`∂/∂x_{ij}` is the derivative in the direction of the unit matrix `E^{ij}` (as in the proof, which
differentiates Leibniz's formula (4.22) in the entries). Symmetrized directions are *not* used here. -/
theorem lemma_4_17 {d : ℕ} (y : Mat d) (hy : PSD y) (hdiag : ∀ i j : Fin d, i ≠ j → y i j = 0) :
    (∀ i j : Fin d, fderiv ℝ (fun x : Mat d => (Matrix.of x).det) y (E i j) =
      if i = j then ∏ k ∈ Finset.univ.erase i, y k k else 0) ∧
    (∀ i j : Fin d, i < j →
      fderiv ℝ (fun z : Mat d => fderiv ℝ (fun x : Mat d => (Matrix.of x).det) z (E i j)) y (E j i) =
        - ∏ k ∈ (Finset.univ.erase i).erase j, y k k) ∧
    (∀ i j : Fin d, i ≤ j →
      fderiv ℝ (fun z : Mat d => fderiv ℝ (fun x : Mat d => (Matrix.of x).det) z (E i j)) y (E i j) =
        0) := by sorry

end AffinePSD.Necessity
