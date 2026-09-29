-- Prove2me | Theorems.Thm_DoubleComplex_exists_HTot_equiv_of_levelwise_equiv_pinned
-- name    : DoubleComplex.exists_HTot_equiv_of_levelwise_equiv_pinned
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/9ec29ded-7a70-5d72-8f1a-0e76d1a172dd
-- title:
--   Pinned functoriality of total cohomology of double complexes
-- statement:
--   Let $R$ be a commutative ring and let $D$, $D'$ be bounded double complexes of $R$-modules in the sense of [`DoubleComplex.Bounded`](def/AlgebraicGeometry_DoubleComplex.html#L11): bigraded families $D^{p,q}$ ($p,q\in\mathbb{N}$) of $R$-modules with horizontal maps $d_H\colon D^{p,q}\to D^{p+1,q}$ and vertical maps $d_V\colon D^{p,q}\to D^{p,q+1}$, each squaring to zero and commuting with each other ($d_V\circ d_H=d_H\circ d_V$), together with an $N$ such that $D^{p,q}$ is a subsingleton whenever $N\le p$ or $N\le q$. Suppose given $R$-linear isomorphisms $e_{p,q}\colon D^{p,q}\xrightarrow{\sim}D'^{p,q}$ for all $p,q$ satisfying $e_{p+1,q}(d_H x)=d_H(e_{p,q}x)$ and $e_{p,q+1}(d_V x)=d_V(e_{p,q}x)$ for all $x\in D^{p,q}$. Then for each $n\in\mathbb{N}$ there is an $R$-linear isomorphism $E$ from $\mathrm{HTot}\,D\,n$ to $\mathrm{HTot}\,D'\,n$, where $\mathrm{HTot}$ is the quotient of $\ker(d_{\mathrm{Tot}}^n)$ by `HTotB` ($\bot$ for $n=0$, and otherwise the preimage under the inclusion of the image of $d_{\mathrm{Tot}}^{n-1}$), with $d_{\mathrm{Tot}}$ acting on $\prod_{p+q=n}D^{p,q}$ componentwise as $d_H+(-1)^p d_V$, such that moreover for every $c\in\ker(d_{\mathrm{Tot}}^n)$ the levelwise image $i\mapsto e_{i_1,i_2}(c_i)$ again lies in $\ker(d_{\mathrm{Tot}}^n$ for $D')$ and $E$ sends the class of $c$ to the class of that element.
--
--   This is the functoriality of the total cohomology of a bounded double complex in a levelwise isomorphism of double complexes, in a pinned form: the induced isomorphism is specified on classes of cocycles, not merely asserted to exist. It is used in the Čech-theoretic part of the development, for comparison of bi-Čech total cohomology with product covers and cup products and for the Künneth-type injectivity statements for $\mathcal{O}$-module presheaves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DoubleComplex_exists_HTot_equiv_of_levelwise_equiv_pinned.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem DoubleComplex.exists_HTot_equiv_of_levelwise_equiv_pinned
    {R : Type u} [CommRing R] (D D' : DoubleComplex.Bounded R)
    (e : ∀ p q : ℕ, D.C p q ≃ₗ[R] D'.C p q)
    (hH : ∀ (p q : ℕ) (x : D.C p q), e (p + 1) q (D.dH p q x) = D'.dH p q (e p q x))
    (hV : ∀ (p q : ℕ) (x : D.C p q), e p (q + 1) (D.dV p q x) = D'.dV p q (e p q x))
    (n : ℕ) :
    ∃ E : DoubleComplex.HTot D n ≃ₗ[R] DoubleComplex.HTot D' n,
      ∀ c : ↥(LinearMap.ker (DoubleComplex.dTot D n)),
        ∃ hc : (fun i : DoubleComplex.Diag n => e i.1.1 i.1.2 (c.1 i)) ∈ LinearMap.ker (DoubleComplex.dTot D' n),
          E (Submodule.Quotient.mk c) = Submodule.Quotient.mk ⟨_, hc⟩ := by sorry
