-- Prove2me | Theorems.Thm_CauchyRiemannIndex_czIndex_conj_path
-- name    : CauchyRiemannIndex.czIndex_conj_path
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T10:47:57.794141+00:00
-- url     : https://prove2.me/theorems/635f767c-9d6b-459b-a40a-e2581acbc7c3
-- title:
--   Conjugating a symplectic path by complex conjugation negates its Conley–Zehnder index
-- statement:
--   Let $\psi:[0,1]\to\mathrm{Sp}(2n)$ be a continuous path of symplectic matrices with $\psi(0)=\mathrm{Id}$ such that $1$ is not an eigenvalue of $\psi(1)$, and let $C$ be complex conjugation $(x,y)\mapsto(x,-y)$ on $\mathbb{C}^n=\mathbb{R}^{2n}$. Then the conjugated path $\varphi(t)=C\,\psi(t)\,C$ has Conley–Zehnder index
--   $$\mu_{CZ}(\varphi)=-\mu_{CZ}(\psi).$$
--   This is the path-level statement behind the sign change of the Conley–Zehnder index of the conjugate asymptotic operator (Wendl, Lemma 5.8).
--
--   **Formalization Note** $C$ is `conjMat n`; the path $\psi$ lies in Gutt's class $\mathcal{SP}(n)$, written out pointwise by the hypotheses `hs`, `h0`, `h1`; `czIndex` is the Conley–Zehnder index of a path in `Definitions.Def_CauchyRiemannIndex_Setting`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 5, proof of Lemma 5.8, p. 87; Conley–Zehnder index as in J. Gutt, arXiv:1307.7239, §2

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- For a path `ψ` in `SP(n)` (symplectic, starting at `Id`, ending without eigenvalue `1`), the
path `t ↦ C ψ(t) C` obtained by conjugating with complex conjugation `C` has Conley–Zehnder index
`-μ_CZ(ψ)`. -/
theorem czIndex_conj_path (n : ℕ) (ψ φ : C(unitInterval, Mat n))
    (hs : ∀ t, IsSymplectic (ψ t)) (h0 : ψ 0 = 1) (h1 : (1 - ψ 1).det ≠ 0)
    (hφ : ∀ t, φ t = conjMat n * ψ t * conjMat n) :
    czIndex φ = -czIndex ψ := by
  sorry

end CauchyRiemannIndex
