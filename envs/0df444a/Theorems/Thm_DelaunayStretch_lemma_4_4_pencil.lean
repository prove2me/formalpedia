-- Prove2me | Theorems.Thm_DelaunayStretch_lemma_4_4_pencil
-- name    : DelaunayStretch.lemma_4_4_pencil
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:54:26.04676+00:00
-- url     : https://prove2.me/theorems/92d69fd5-8f5d-4433-a3a6-8078279226fc
-- title:
--   Lemma 4.4 — pencil lemma: the disks through two points, derivatives (4.5), and $\frac{d}{dX}W_{H,U}(s(X))=\mathcal E_U[H;\nabla]$
-- statement:
--   Let $G=[a_G,b_G]$ be a segment with $y(a_G)>0>y(b_G)$, midpoint $M$ and unit normal $\nu$ with positive $x$-component; for $X\in\mathbb R$ let $O(X)$ be the closed disk with center $o(X)=M+X\nu$ and radius $r(X)=\sqrt{X^2+|G|^2/4}$.
--
--   1. The closed disks whose boundary passes through $a_G$ and $b_G$ are exactly the disks $O(X)$. For $X_1\ne X_2$ the circles $\partial O(X_1)$, $\partial O(X_2)$ meet exactly in $a_G$ and $b_G$, and $x(o(X_2))>x(o(X_1))$ if and only if $X_2>X_1$.
--   2. Let $\delta\in[-|G|,|G|]$. For every $X$, $s(X)=(O(X),G,\delta)$ is a gate state; its angular coordinates $z(X)=(\gamma,\varphi,\theta,\psi)$ are smooth in $X$, $\varphi$ does not depend on $X$, and
--   $$
--   r'=\cos\theta,\qquad r\gamma'=\mathcal A,\qquad r\theta'=-\sin\theta,\qquad r\psi'=-(\psi-\varphi)\cos\theta .
--   $$
--   3. Let $U\in\mathbb R$, $H$ a real function on $\Omega\times\mathbb R$, $X_0\in\mathbb R$ and $\nabla\in\mathbb R^4$ with $(H\circ z)'(X_0)=\nabla\cdot z'(X_0)$. Then $X\mapsto W_{H,U}(s(X))$ is differentiable at $X_0$ with derivative $\mathcal E_U[H;\nabla](z(X_0))$; in particular, if $H$ is differentiable at $z(X_0)$, the derivative is $\mathcal E_U[H](z(X_0))$.
--
--   The lemma turns the infinitely many next disks of a step into one differential inequality, condition (H4).
--
--   **Formalization Note** "Smooth" is $C^\infty$, stated for each of the four coordinates; the identities (4.5) are stated with the derivative, which exists by smoothness.
--
--   Differences from the source:
--   - encoding: smooth functions of X → C^∞ (ContDiff ℝ ⊤ with ⊤ : ℕ∞) for each coordinate; reason: smooth means C^∞
--   - encoding: points of ℝ² with coordinates x(z), y(z) and Euclidean norm → points of ℂ with x = re, y = im and ‖z − w‖ = dist z w; reason: ℂ is ℝ² with the Euclidean norm; same instances
--   - encoding: H a real function on Ω × ℝ → H : ℝ⁴ → ℝ, z = (γ, φ, θ, ψ); every hypothesis and conclusion reads H only on Ω × ℝ (on Σ for gate states); reason: Ω × ℝ is open in ℝ⁴, so values and derivatives of H there do not depend on the values outside; same functions
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Lemma 4.4, p.25

import Mathlib
import Definitions.Def_DelaunayStretch_potential
import Definitions.Def_DelaunayStretch_pencilDisk

namespace DelaunayStretch

/-- **Lemma 4.4 (Pencil lemma)** (p.25). Let `G = [aG, bG]` be a segment with
`y(aG) > 0 > y(bG)`, midpoint `M`, and unit normal vector `ν` with positive `x`-component. For
`X ∈ ℝ`, let `O(X)` be the closed disk with center `o(X) = M + Xν` and radius
`r(X) = √(X² + |G|²/4)`.

1. The closed disks whose boundary passes through `aG` and `bG` are exactly the disks `O(X)`,
   `X ∈ ℝ`. For `X₁ ≠ X₂`, the circles `∂O(X₁)` and `∂O(X₂)` meet exactly in `aG` and `bG`, and
   `x(o(X₂)) > x(o(X₁))` if and only if `X₂ > X₁`.
2. Let `δ ∈ [−|G|, |G|]`. For every `X ∈ ℝ`, the triple `s(X) = (O(X), G, δ)` is a gate state.
   Its angular coordinates `z(X) = (γ, φ, θ, ψ)` are smooth functions of `X`, `φ` does not
   depend on `X`, and `r′ = cos θ`, `rγ′ = 𝓐`, `rθ′ = −sin θ`, `rψ′ = −(ψ − φ) cos θ` (4.5),
   where `r = r(X)` and the prime denotes `d/dX`.
3. Let `δ`, `s(X)`, `z(X)` be as in (2), let `U ∈ ℝ`, let `H` be a real function on `Ω × ℝ`,
   and let `X₀ ∈ ℝ` and `∇ ∈ ℝ⁴` be such that `H ∘ z` is differentiable at `X₀` with
   `(H ∘ z)′(X₀) = ∇ · z′(X₀)`. Then `X ↦ W_{H,U}(s(X))` is differentiable at `X₀`, and its
   derivative there is `𝓔_U[H; ∇](z(X₀))`. In particular, if `H` is differentiable at `z(X₀)`,
   the derivative is `𝓔_U[H](z(X₀))`.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026), Lemma 4.4, p.25.

**Formalization Note** A closed disk is a `Disk` (center, radius); the disks `O(X)` are
`pencilDisk aG bG X`. "Smooth" is `C^∞` (`ContDiff ℝ ⊤` with `⊤ : ℕ∞`) for each of the four
coordinates. `z′(X₀)` is `deriv z X₀` in `ℝ⁴`; the derivative identities are stated with
`deriv`, which is the derivative since the coordinates are smooth. -/
theorem lemma_4_4_pencil (aG bG : ℂ) (ha : 0 < aG.im) (hb : bG.im < 0) :
    (∀ O : Disk, (aG ∈ O.boundary ∧ bG ∈ O.boundary) ↔ ∃ X : ℝ, O = pencilDisk aG bG X) ∧
    (∀ X₁ X₂ : ℝ, X₁ ≠ X₂ →
      (pencilDisk aG bG X₁).boundary ∩ (pencilDisk aG bG X₂).boundary = {aG, bG} ∧
        ((pencilDisk aG bG X₁).center.re < (pencilDisk aG bG X₂).center.re ↔ X₁ < X₂)) ∧
    (∀ δ : ℝ, |δ| ≤ dist aG bG →
      (∀ X : ℝ, (pencilState aG bG δ X).IsGateState) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun X => (pencilState aG bG δ X).gammaCoord) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun X => (pencilState aG bG δ X).phiCoord) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun X => (pencilState aG bG δ X).thetaCoord) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun X => (pencilState aG bG δ X).psiCoord) ∧
      (∀ X₁ X₂ : ℝ, (pencilState aG bG δ X₁).phiCoord = (pencilState aG bG δ X₂).phiCoord) ∧
      (∀ X : ℝ,
        deriv (fun Y => (pencilDisk aG bG Y).radius) X = Real.cos (pencilState aG bG δ X).thetaCoord ∧
        (pencilDisk aG bG X).radius * deriv (fun Y => (pencilState aG bG δ Y).gammaCoord) X =
          pencilA (pencilState aG bG δ X).angularCoords ∧
        (pencilDisk aG bG X).radius * deriv (fun Y => (pencilState aG bG δ Y).thetaCoord) X =
          -Real.sin (pencilState aG bG δ X).thetaCoord ∧
        (pencilDisk aG bG X).radius * deriv (fun Y => (pencilState aG bG δ Y).psiCoord) X =
          -((pencilState aG bG δ X).psiCoord - (pencilState aG bG δ X).phiCoord) *
            Real.cos (pencilState aG bG δ X).thetaCoord) ∧
      (∀ (U : ℝ) (H : R4 → ℝ) (X₀ : ℝ) (g : R4),
        HasDerivAt (fun X => H (pencilState aG bG δ X).angularCoords)
          (dot4 g (deriv (fun X => (pencilState aG bG δ X).angularCoords) X₀)) X₀ →
        HasDerivAt (fun X => potential H U (pencilState aG bG δ X))
          (pencilResidual U H g (pencilState aG bG δ X₀).angularCoords) X₀) ∧
      (∀ (U : ℝ) (H : R4 → ℝ) (X₀ : ℝ),
        DifferentiableAt ℝ H (pencilState aG bG δ X₀).angularCoords →
        HasDerivAt (fun X => potential H U (pencilState aG bG δ X))
          (pencilResidualGrad U H (pencilState aG bG δ X₀).angularCoords) X₀)) := by sorry

end DelaunayStretch
