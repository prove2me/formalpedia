-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq
-- name    : AlgebraicGeometry.OModulePresheaf.exists_forall_res_basicOpen_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/4e369311-4313-5476-96e4-2e766dfca472
-- title:
--   Gluing over a finite basic-open cover of an affine open
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme, $\pi : V \to \operatorname{Spec} R$ a morphism, and $F$ an `OModulePresheaf` over $\pi$: an assignment to each open $U \subseteq V$ of a type $F(U)$ carrying an abelian group structure, an $R$-module structure and a $\Gamma(V,U)$-module structure compatible with the $R$-algebra structure on $\Gamma(V,U)$ induced by $\pi$, together with $R$-linear restrictions $F(U') \to F(U)$ for $U \le U'$ which are semilinear for restriction of functions ($\mathrm{res}(a\cdot x) = (a|_U)\cdot \mathrm{res}(x)$) and functorial (identity on $U \le U$, composing along $U \le U' \le U''$). Assume `hF`, quasicoherence in the elementwise sense: for every affine open $U$ and every $f \in \Gamma(V,U)$, each $x \in F(D(f))$ satisfies $\mathrm{res}(y) = (f^n|_{D(f)})\cdot x$ for some $n \in \mathbb{N}$ and $y \in F(U)$, and every $y \in F(U)$ with $\mathrm{res}(y) = 0$ in $F(D(f))$ is killed by some power $f^n$. Let $U$ be an affine open of $V$, $\iota$ a finite type, $h : \iota \to \Gamma(V,U)$ with $U \le \bigsqcup_j D(h_j)$, and let $x_j \in F(D(h_j))$ agree on overlaps, i.e. the two restrictions of $x_j$ and $x_k$ to $D(h_j h_k) = D(h_j) \cap D(h_k)$ coincide for all $j,k$. Then there exists $y \in F(U)$ with $\mathrm{res}(y) = x_j$ in $F(D(h_j))$ for every $j$.
--
--   This is the existence (gluing) half of the sheaf condition for quasi-coherent module data with respect to a finite cover of an affine open by basic opens; the complementary separatedness statement gives uniqueness of $y$. It is used in the identification of the kernel of the zeroth Čech differential for such module data, via [`AlgebraicGeometry.OModulePresheaf.internalHom_d_zero_eq_zero_iff_existsUnique`](thm.html#AlgebraicGeometry.OModulePresheaf.internalHom_d_zero_eq_zero_iff_existsUnique).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_res_basicOpen_eq
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F : OModulePresheaf π}
    (hF : F.IsQuasicoherent) (U : V.affineOpens) {ι : Type*} [Fintype ι] (h : ι → Γ(V, U.1))
    (hcov : U.1 ≤ ⨆ j, V.basicOpen (h j)) (x : ∀ j, F.obj (V.basicOpen (h j)))
    (hx : ∀ j k, F.res ((V.basicOpen_mul (h j) (h k)).trans_le inf_le_left) (x j) =
      F.res ((V.basicOpen_mul (h j) (h k)).trans_le inf_le_right) (x k)) :
    ∃ y : F.obj U.1, ∀ j, F.res (V.basicOpen_le (h j)) y = x j := by sorry
