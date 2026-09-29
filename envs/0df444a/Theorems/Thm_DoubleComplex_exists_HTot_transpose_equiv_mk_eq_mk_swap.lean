-- Prove2me | Theorems.Thm_DoubleComplex_exists_HTot_transpose_equiv_mk_eq_mk_swap
-- name    : DoubleComplex.exists_HTot_transpose_equiv_mk_eq_mk_swap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/308c0727-d5ba-53d4-a697-43132d1e0582
-- title:
--   Signed transposition on total cohomology of a bounded double complex
-- statement:
--   Fix a universe and a commutative ring $R$, and let $D$ be a bounded double complex of $R$-modules in the project's sense: a family of $R$-modules $C^{p,q}$ indexed by $p,q\in\mathbb{N}$, $R$-linear maps $d_H\colon C^{p,q}\to C^{p+1,q}$ and $d_V\colon C^{p,q}\to C^{p,q+1}$ with $d_H^2=0$, $d_V^2=0$ and $d_V d_H=d_H d_V$, together with a bound $N$ such that $C^{p,q}$ is a subsingleton whenever $N\le p$ or $N\le q$. For $n\in\mathbb{N}$ write $\mathrm{Tot}(D)^n=\prod_{p+q=n}C^{p,q}$, with total differential $d_{\mathrm{Tot}}$ whose $(p,q)$-component is $d_H+(-1)^p d_V$ applied to the appropriate neighbouring components (the components with $p=0$, resp. $q=0$, contributing zero), and let $\mathrm{HTot}(D)^n$ be the quotient of $\ker d_{\mathrm{Tot}}^n$ by the submodule of those cocycles lying in the image of $d_{\mathrm{Tot}}^{n-1}$ (by $\bot$ when $n=0$). Let $D^{t}$ be the transposed complex, $C_{D^t}^{a,b}=C_D^{b,a}$ with $d_H$ and $d_V$ interchanged. The assertion is that for every $n$ there exists an $R$-linear isomorphism $e\colon \mathrm{HTot}(D^{t})^n\xrightarrow{\sim}\mathrm{HTot}(D)^n$ such that for every $z\in\mathrm{Tot}(D^{t})^n$ with $d_{\mathrm{Tot}}^n z=0$, the signed swap $Sz$ defined by $(Sz)^{p,q}=(-1)^{pq}z^{q,p}$ again lies in $\ker d_{\mathrm{Tot}}^n$ for $D$, and $e$ sends the class of $z$ to the class of $Sz$.
--
--   This is the sign-trick comparison between the total complexes of a double complex and of its transpose, in a form that pins down the effect on cohomology classes by an explicit formula rather than merely asserting the existence of an isomorphism. It is used in the comparison of iterated Čech constructions, namely for the Künneth-type cup comparison [`AlgebraicGeometry.OModulePresheaf.exists_HTot_biCech_equiv_prodCover_cup_pinned`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_HTot_biCech_equiv_prodCover_cup_pinned) and for [`AlgebraicGeometry.OModulePresheaf.exists_HSucc_equiv_unitPullback_id_of_isSeparated`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_HSucc_equiv_unitPullback_id_of_isSeparated), where it matters where a specific class is sent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DoubleComplex_exists_HTot_transpose_equiv_mk_eq_mk_swap.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem DoubleComplex.exists_HTot_transpose_equiv_mk_eq_mk_swap
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R) (n : ℕ) :
    ∃ e : DoubleComplex.HTot (DoubleComplex.transpose D) n ≃ₗ[R] DoubleComplex.HTot D n,
      ∀ (z : DoubleComplex.Tot (DoubleComplex.transpose D) n)
        (hz : z ∈ LinearMap.ker (DoubleComplex.dTot (DoubleComplex.transpose D) n)),
        ∃ hSz : (fun pq : DoubleComplex.Diag n =>
            ((-1 : ℤ) ^ (pq.1.1 * pq.1.2)) • (show D.C pq.1.1 pq.1.2 from z ⟨(pq.1.2, pq.1.1), by have := pq.2; omega⟩))
              ∈ LinearMap.ker (DoubleComplex.dTot D n),
          e (Submodule.Quotient.mk ⟨z, hz⟩) = Submodule.Quotient.mk ⟨_, hSz⟩ := by sorry
