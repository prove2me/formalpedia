-- Prove2me | Theorems.Thm_CauchyRiemannIndex_symplecticLoop_fixing_vector_homotopic_diamond
-- name    : CauchyRiemannIndex.symplecticLoop_fixing_vector_homotopic_diamond
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T16:49:25.240535+00:00
-- url     : https://prove2.me/theorems/85d88df2-c21d-4555-aecb-e7b5a30f3dcf
-- title:
--   Symplectic loops fixing a basis vector are homotopic to loops in $\mathrm{Sp}(2n)\diamond\mathrm{Id}$
-- statement:
--   Let $B:[0,1]\to\mathrm{Sp}(2n+2,\mathbb R)$ be a continuous loop with $B(0)=B(1)=\mathrm{Id}$ such that $B(t)e=e$ for all $t$, where $e$ is the last basis vector of the $q$-block of $\mathbb R^{2n+2}=\mathbb R^{n+1}_q\times\mathbb R^{n+1}_p$. Then there are a continuous loop $B':[0,1]\to\mathrm{Sp}(2n,\mathbb R)$ with $B'(0)=B'(1)=\mathrm{Id}$ and a continuous $\Phi:[0,1]\times[0,1]\to\mathrm{Sp}(2n+2,\mathbb R)$ with
--   $$\Phi(0,t)=B(t),\qquad \Phi(1,t)=B'(t)\diamond\mathrm{Id}_{2},\qquad \Phi(s,0)=\Phi(s,1)=\mathrm{Id}.$$
--   Here $A\diamond C$ is the block-diagonal embedding $\mathrm{Sp}(2n)\times\mathrm{Sp}(2)\to\mathrm{Sp}(2n+2)$, $(q',p')\oplus(q'',p'')\mapsto(q',q'',p',p'')$.
--
--   Thus every based loop in the stabiliser of $e$ is homotopic, through based symplectic loops, to a loop coming from $\mathrm{Sp}(2n)$.
--
--   **Formalization Note.** $\mathbb R^{2n\times2n}$ is `Mat n` (real matrices indexed by `Fin n ⊕ Fin n`, first block $q$, second block $p$) and $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ is `Matrix.J`; `IsSymplectic A` is membership in `Matrix.symplecticGroup`. Vectors of $\mathbb R^{2n}$ are functions `Fin n ⊕ Fin n → ℝ` and $Av$ is `A *ᵥ v`. $e$ is `Pi.single (Sum.inl (Fin.last n)) 1`, and $A\diamond C$ is `ConleyZehnder.diamond A C` from the Conley-Zehnder setting definitions (`Mat` there is the same type), here with `C = (1 : Mat 1)`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, p. 62 (Theorem 3.34 and the Maslov index of loops in $\mathrm{Sp}(2n)$); J. Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse 23 (2014), arXiv:1307.7239, §2 (the map $\hat\rho$, eq. (9))

import Definitions.Def_CauchyRiemannIndex_Setting
import Definitions.Def_ConleyZehnder_Setting

namespace CauchyRiemannIndex

open Matrix

/-- A loop in `Sp(2n + 2)` based at `Id` that fixes the basis vector `e = q_{n+1}` is homotopic,
through loops in `Sp(2n + 2)` based at `Id`, to a loop `B' ⋄ Id` with `B'` a loop in `Sp(2n)`
based at `Id`. -/
theorem symplecticLoop_fixing_vector_homotopic_diamond (n : ℕ)
    (B : C(unitInterval, Mat (n + 1))) (hs : ∀ t, IsSymplectic (B t)) (h0 : B 0 = 1)
    (h1 : B 1 = 1)
    (he : ∀ t, B t *ᵥ Pi.single (Sum.inl (Fin.last n)) 1 = Pi.single (Sum.inl (Fin.last n)) 1) :
    ∃ B' : C(unitInterval, Mat n), (∀ t, IsSymplectic (B' t)) ∧ B' 0 = 1 ∧ B' 1 = 1 ∧
      ∃ Φ : C(unitInterval × unitInterval, Mat (n + 1)), (∀ t, Φ (0, t) = B t) ∧
        (∀ t, Φ (1, t) = ConleyZehnder.diamond (B' t) (1 : Mat 1)) ∧
        (∀ s t, IsSymplectic (Φ (s, t))) ∧ (∀ s, Φ (s, 0) = 1) ∧ ∀ s, Φ (s, 1) = 1 := by sorry

end CauchyRiemannIndex
