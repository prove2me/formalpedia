-- Prove2me | Theorems.Thm_CauchyRiemannIndex_symplecticPath_family_of_czIndex_eq
-- name    : CauchyRiemannIndex.symplecticPath_family_of_czIndex_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T12:51:24.336825+00:00
-- url     : https://prove2.me/theorems/cd871305-912a-4dd0-a268-bcdc531ac6a1
-- title:
--   Paths in $SP(n)$ with the same Conley–Zehnder index are joined inside $SP(n)$
-- statement:
--   Let $SP(n)$ be the set of continuous paths $\psi:[0,1]\to\mathrm{Sp}(2n,\mathbb R)$ with $\psi(0)=\mathrm{Id}$ such that $1$ is not an eigenvalue of $\psi(1)$, and let $\mu_{CZ}:SP(n)\to\mathbb Z$ be the Conley–Zehnder index. If $\psi_0,\psi_1\in SP(n)$ satisfy
--   $$\mu_{CZ}(\psi_0)=\mu_{CZ}(\psi_1),$$
--   then there is a continuous map $G:[0,1]\times[0,1]\to\mathbb R^{2n\times2n}$ with $G(0,\cdot)=\psi_0$, $G(1,\cdot)=\psi_1$ and $G(s,\cdot)\in SP(n)$ for every $s\in[0,1]$.
--
--   Together with the homotopy invariance of the index, this is the classical statement that the Conley–Zehnder index classifies the path components of $SP(n)$ (the homotopy classes of nondegenerate symplectic arcs; Wendl, Lecture 3, p. 62).
--
--   **Formalization Note.** $\mathbb R^{2n\times2n}$ is `Mat n` (real matrices indexed by `Fin n ⊕ Fin n`) and $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ is `Matrix.J`. The paths are `ψ₀ ψ₁ : C(unitInterval, Mat n)`; membership in $SP(n)$ is written out as `∀ t, IsSymplectic (ψ t)`, `ψ 0 = 1` and `(1 - ψ 1).det ≠ 0`, and the index is `czIndex` from the setting definitions (Gutt, Definition 7, chosen with fallback $0$). The family is `G : C(unitInterval × unitInterval, Mat n)`; the conditions on each $G(s,\cdot)$ are stated pointwise in the same form.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, p. 62 (the classification of homotopy classes of nondegenerate symplectic arcs by the Conley-Zehnder index, stated before Theorem 3.34); index as in J. Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse 23 (2014), arXiv:1307.7239, Definition 7

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Two paths in `SP(n)` with the same Conley–Zehnder index are joined by a continuous family
of paths in `SP(n)`. -/
theorem symplecticPath_family_of_czIndex_eq (n : ℕ) (ψ₀ ψ₁ : C(unitInterval, Mat n))
    (hs₀ : ∀ t, IsSymplectic (ψ₀ t)) (h0₀ : ψ₀ 0 = 1) (h1₀ : (1 - ψ₀ 1).det ≠ 0)
    (hs₁ : ∀ t, IsSymplectic (ψ₁ t)) (h0₁ : ψ₁ 0 = 1) (h1₁ : (1 - ψ₁ 1).det ≠ 0)
    (h : czIndex ψ₀ = czIndex ψ₁) :
    ∃ G : C(unitInterval × unitInterval, Mat n), (∀ t, G (0, t) = ψ₀ t) ∧
      (∀ t, G (1, t) = ψ₁ t) ∧ (∀ s t, IsSymplectic (G (s, t))) ∧ (∀ s, G (s, 0) = 1) ∧
      ∀ s, (1 - G (s, 1)).det ≠ 0 := by
  sorry

end CauchyRiemannIndex
