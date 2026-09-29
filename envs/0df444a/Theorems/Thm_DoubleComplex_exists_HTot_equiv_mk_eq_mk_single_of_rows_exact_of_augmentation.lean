-- Prove2me | Theorems.Thm_DoubleComplex_exists_HTot_equiv_mk_eq_mk_single_of_rows_exact_of_augmentation
-- name    : DoubleComplex.exists_HTot_equiv_mk_eq_mk_single_of_rows_exact_of_augmentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/5173a533-415b-517b-9f5b-ec1a640b5c57
-- title:
--   Pinned edge isomorphism Hⁿ(A) ≅ Hⁿ(Tot D)
-- statement:
--   Let $R$ be a commutative ring and let $D$ be a bounded double complex of $R$-modules in the sense of [`DoubleComplex.Bounded`](def/AlgebraicGeometry_DoubleComplex.html#L11): modules $C^{p,q}$ for $p,q \in \mathbb{N}$, horizontal maps $d_H^{p,q} \colon C^{p,q} \to C^{p+1,q}$ and vertical maps $d_V^{p,q} \colon C^{p,q} \to C^{p,q+1}$, each squaring to zero, commuting with one another, and with an $N$ such that $C^{p,q}$ is subsingleton whenever $N \le p$ or $N \le q$. Let $A^m$ ($m \in \mathbb{N}$) be $R$-modules with $R$-linear maps $d_A^m \colon A^m \to A^{m+1}$ (no condition $d_A \circ d_A = 0$ is imposed; it follows from the hypotheses below), and let $\varepsilon^m \colon A^m \to C^{0,m}$ be $R$-linear maps such that each $\varepsilon^m$ is injective, $d_V^{0,m} \circ \varepsilon^m = \varepsilon^{m+1} \circ d_A^m$, $\ker d_H^{0,m} = \operatorname{im} \varepsilon^m$, and every row is exact in positive horizontal degree: $\ker d_H^{p+1,m} \le \operatorname{im} d_H^{p,m}$ for all $p,m$. Here $\operatorname{Tot}^n D$ is the product of the $C^{p,q}$ over the diagonal $p+q=n$, $d_{\mathrm{Tot}}^n$ has component at $(p,q)$ given by $d_H$ plus $(-1)^p d_V$ from the neighbouring diagonal entries, and [`DoubleComplex.HTot D n`](def/AlgebraicGeometry_DoubleComplex.html#L65) is $\ker d_{\mathrm{Tot}}^n$ modulo $\bot$ for $n = 0$ and modulo the preimage of $\operatorname{im} d_{\mathrm{Tot}}^{n-1}$ for $n > 0$. The conclusion is twofold. First, there is an $R$-linear isomorphism $e \colon \ker d_A^0 \to$ `HTot D 0` such that for every $a \in \ker d_A^0$ the element of $\operatorname{Tot}^0 D$ with value $\varepsilon^0 a$ at the index $(0,0)$ and $0$ elsewhere lies in $\ker d_{\mathrm{Tot}}^0$ and $e(a)$ is its class. Second, for every $n$ there is an $R$-linear isomorphism $e$ from $\ker d_A^{n+1}$ modulo the preimage of $\operatorname{im} d_A^{n}$ in $\ker d_A^{n+1}$ onto `HTot D (n+1)` such that for every $a \in \ker d_A^{n+1}$ the element of $\operatorname{Tot}^{n+1} D$ with value $\varepsilon^{n+1} a$ at the index $(0,n+1)$ and $0$ elsewhere is a $d_{\mathrm{Tot}}$-cocycle, and $e$ sends the class of $a$ to the class of that element.
--
--   This is the staircase (edge homomorphism) comparison for a bounded first-quadrant double complex with exact augmented rows, in the form that pins down the isomorphism on classes: the cohomology of the augmentation complex $A^\bullet$ is computed by the total complex, via the map sending a cocycle $a$ to the class of $\varepsilon a$ placed in the column $p=0$. The pinned form is what allows classes to be tracked through iterated Čech constructions, and it is used by [`AlgebraicGeometry.OModulePresheaf.exists_HSucc_equiv_unitPullback_id_of_isSeparated`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_HSucc_equiv_unitPullback_id_of_isSeparated) and by the cup-product comparison [`AlgebraicGeometry.OModulePresheaf.exists_HTot_biCech_equiv_prodCover_cup_pinned`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_HTot_biCech_equiv_prodCover_cup_pinned).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DoubleComplex_exists_HTot_equiv_mk_eq_mk_single_of_rows_exact_of_augmentation.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem DoubleComplex.exists_HTot_equiv_mk_eq_mk_single_of_rows_exact_of_augmentation
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R)
    (A : ℕ → Type u) [∀ m, AddCommGroup (A m)] [∀ m, Module R (A m)]
    (dA : ∀ m, A m →ₗ[R] A (m + 1)) (ε : ∀ m, A m →ₗ[R] D.C 0 m)
    (hε : ∀ m, Function.Injective (ε m))
    (hεd : ∀ m, D.dV 0 m ∘ₗ ε m = ε (m + 1) ∘ₗ dA m)
    (hker : ∀ m, LinearMap.ker (D.dH 0 m) = LinearMap.range (ε m))
    (hrows : ∀ p m, LinearMap.ker (D.dH (p + 1) m) ≤ LinearMap.range (D.dH p m)) :
    (∃ e : LinearMap.ker (dA 0) ≃ₗ[R] DoubleComplex.HTot D 0,
        ∀ (a : A 0) (ha : a ∈ LinearMap.ker (dA 0)),
          ∃ hE : Pi.single (M := fun i : DoubleComplex.Diag 0 => D.C i.1.1 i.1.2) ⟨(0, 0), rfl⟩ (ε 0 a)
              ∈ LinearMap.ker (DoubleComplex.dTot D 0),
            e ⟨a, ha⟩ = Submodule.Quotient.mk ⟨_, hE⟩) ∧
      ∀ n : ℕ, ∃ e : (LinearMap.ker (dA (n + 1)) ⧸
            (LinearMap.range (dA n)).comap (LinearMap.ker (dA (n + 1))).subtype) ≃ₗ[R] DoubleComplex.HTot D (n + 1),
        ∀ (a : A (n + 1)) (ha : a ∈ LinearMap.ker (dA (n + 1))),
          ∃ hE : Pi.single (M := fun i : DoubleComplex.Diag (n + 1) => D.C i.1.1 i.1.2) ⟨(0, n + 1), by omega⟩ (ε (n + 1) a)
              ∈ LinearMap.ker (DoubleComplex.dTot D (n + 1)),
            e (Submodule.Quotient.mk ⟨a, ha⟩) = Submodule.Quotient.mk ⟨_, hE⟩ := by sorry
