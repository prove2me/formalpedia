-- Prove2me | Theorems.Thm_CauchyRiemannIndex_spStar_joinedIn_of_sign_det_eq
-- name    : CauchyRiemannIndex.spStar_joinedIn_of_sign_det_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T15:38:33.262039+00:00
-- url     : https://prove2.me/theorems/d5bacb9a-2f7a-42d5-823d-4d72f77390f8
-- title:
--   Points of $\mathrm{Sp}^*(2n)$ with the same sign of $\det(\mathrm{Id}-A)$ lie in one path component
-- statement:
--   Let $\mathrm{Sp}^*(2n)=\{A\in\mathrm{Sp}(2n,\mathbb R):\det(\mathrm{Id}-A)\neq0\}$ be the set of symplectic matrices without eigenvalue $1$. If $A,B\in\mathrm{Sp}^*(2n)$ satisfy
--   $$\operatorname{sign}\det(\mathrm{Id}-A)=\operatorname{sign}\det(\mathrm{Id}-B),$$
--   then $A$ and $B$ are joined by a continuous path in $\mathrm{Sp}^*(2n)$.
--
--   Since $\det(\mathrm{Id}-\cdot)$ has constant sign on each path component of $\mathrm{Sp}^*(2n)$, this shows that $\mathrm{Sp}^*(2n)$ has at most two path components, distinguished by that sign (Gutt, §2; Wendl, Lecture 3, §3.4).
--
--   **Formalization Note.** $\mathbb R^{2n\times2n}$ is `Mat n` (real matrices indexed by `Fin n ⊕ Fin n`) and $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ is `Matrix.J`; `IsSymplectic A` is membership in `Matrix.symplecticGroup`. $\mathrm{Sp}^*(2n)$ is `SpStar n` from the setting definitions, the sign is `Real.sign`, and the conclusion is `JoinedIn (SpStar n) A B`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, p. 62; J. Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse 23 (2014), arXiv:1307.7239, §2 (the map $\hat\rho$, eq. (9))

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Data.Real.Sign

namespace CauchyRiemannIndex

open Matrix

/-- Two symplectic matrices without eigenvalue `1` whose values of `det(1 - ·)` have the same
sign lie in the same path component of `Sp*`. -/
theorem spStar_joinedIn_of_sign_det_eq (n : ℕ) (A B : Mat n) (hA : A ∈ SpStar n)
    (hB : B ∈ SpStar n) (h : Real.sign (1 - A).det = Real.sign (1 - B).det) :
    JoinedIn (SpStar n) A B := by
  sorry

end CauchyRiemannIndex
