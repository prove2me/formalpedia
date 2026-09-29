-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_OmegaNr_exists_equiv_of_ringEquiv_frame
-- name    : CerednikDrinfeld.FormalOmega.OmegaNr.exists_equiv_of_ringEquiv_frame
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/99c4d619-7617-5af6-b50c-0f9d9670d901
-- title:
--   Transport of the widehatΩ⊗widehat𝒪^{nr} datum along a frame isomorphism
-- statement:
--   Let $\mathcal O$ and $\mathcal O'$ be commutative rings, $K$ and $K'$ fields that are algebras over $\mathcal O$ and $\mathcal O'$ respectively, and let $e_b\colon\mathcal O\simeq\mathcal O'$ and $e_K\colon K\simeq K'$ be ring isomorphisms with $e_K(\mathrm{alg}_{\mathcal O,K}(x))=\mathrm{alg}_{\mathcal O',K'}(e_b(x))$ for all $x\in\mathcal O$; let $\pi\in\mathcal O$, $\pi'\in\mathcal O'$ with $e_b(\pi)=\pi'$. Let $O^{nr}$ be a commutative $\mathcal O$-algebra with an $\mathcal O$-algebra automorphism $\mathrm{Fr}$ and $v\colon GL_2(K)\to\mathbb Z$ (multiplicatively written) a monoid homomorphism, and let $O'^{nr},\mathrm{Fr}',v'$ be the primed analogues over $\mathcal O',K'$. Assume a ring isomorphism $e_{O}\colon O^{nr}\simeq O'^{nr}$ with $e_O(\mathrm{alg}(x))=\mathrm{alg}(e_b(x))$ for $x\in\mathcal O$ and $e_O\circ\mathrm{Fr}=\mathrm{Fr}'\circ e_O$, and $v'(GL_2(e_K)(g))=v(g)$ for all $g$. Then there is a family $\Psi$ assigning to each commutative ring $B$ carrying both an $\mathcal O$- and an $\mathcal O'$-algebra structure whose structure maps agree via $e_b$ a bijection between the sets of pairs $(\psi,d)$, $\psi\colon O^{nr}\to_{\mathcal O} B$ an algebra map and $d$ a Deligne datum over $(K,\pi)$ on $B$ (a family of submodules $d.\mathrm{line}\,M\subseteq B\otimes_{\mathcal O}M$ indexed by the full lattices $M\subseteq K^2$, with invertible quotients, monotone under inclusions of lattices, equivariant for scalar homotheties, and nondegenerate at every prime of $B$), and the corresponding primed pairs over $(K',\pi',O'^{nr})$, such that: (i) the first leg is $\psi\mapsto\psi\circ e_O^{-1}$, i.e. $(\Psi_B x).1(y)=x.1(e_O^{-1}(y))$; (ii) for all $g\in GL_2(K)$ and all $x,x'$, the primed twisted-action relation at $GL_2(e_K)(g)$ holds of $(\Psi_B x,\Psi_B x')$ — that is, $(\Psi_B x').1=(\Psi_B x).1\circ(\mathrm{Fr}')^{-v'(GL_2(e_K)(g))}$ together with the pullback relation along the inverse matrix on the Deligne legs — if and only if the unprimed relation holds of $(x,x')$ at $g$; (iii) for all $g,x,x'$ the primed pullback relation $d'.\mathrm{line}\,M=(d.\mathrm{line}(g\cdot M))$ pulled back along the base-changed action map holds for the Deligne legs of $\Psi_B x,\Psi_B x'$ at $GL_2(e_K)(g)$ iff it holds for $x.2,x'.2$ at $g$; and (iv) for all such $B,B_1$ and algebra maps $f\colon B\to_{\mathcal O}B_1$, $f'\colon B\to_{\mathcal O'}B_1$ agreeing pointwise, the base-change relation ($d_1.\mathrm{line}\,M$ equals the span of the image of $d.\mathrm{line}\,M$ under $f\otimes\mathrm{id}$) holds for the Deligne legs of $\Psi_{B}x,\Psi_{B_1}x_1$ along $f'$ iff it holds for $x.2,x_1.2$ along $f$. The Deligne leg of $\Psi$ is pinned down only through these equivalences.
--
--   This is the transport statement for the functor underlying $\widehat\Omega\,\hat\otimes\,\widehat{\mathcal O}^{nr}$ in the Čerednik–Drinfeld uniformisation, in the form of a pair consisting of a coefficient leg $O^{nr}\to B$ and a Deligne datum of lines on base-changed lattices: an isomorphism of frames $(\mathcal O,K,\pi,O^{nr},\mathrm{Fr},v)\simeq(\mathcal O',K',\pi',O'^{nr},\mathrm{Fr}',v')$ induces an identification of the two moduli functors matching the twisted $GL_2$-action relation, the pullback relation and the base-change relation. It is used by [`CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_G_bijective_isActBy_iff_isTwistedAct_of_span_eq_of_isNoetherianRing`](thm.html#CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_G_bijective_isActBy_iff_isTwistedAct_of_span_eq_of_isNoetherianRing) to move the descent data between a concrete frame and an abstract one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_OmegaNr_exists_equiv_of_ringEquiv_frame.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.OmegaNr.exists_equiv_of_ringEquiv_frame
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    {𝒪' : Type} [CommRing 𝒪'] {K' : Type} [Field K'] [Algebra 𝒪' K']
    (eb : 𝒪 ≃+* 𝒪') (eK : K ≃+* K') (hcomm : ∀ x : 𝒪, eK (algebraMap 𝒪 K x) = algebraMap 𝒪' K' (eb x))
    {π : 𝒪} {π' : 𝒪'} (hπ : eb π = π')
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K →* Multiplicative ℤ)
    (Onr' : Type) [CommRing Onr'] [Algebra 𝒪' Onr'] (Fr' : Onr' ≃ₐ[𝒪'] Onr')
    (vdet' : Matrix.GeneralLinearGroup (Fin 2) K' →* Multiplicative ℤ)
    (eO : Onr ≃+* Onr') (heO : ∀ x : 𝒪, eO (algebraMap 𝒪 Onr x) = algebraMap 𝒪' Onr' (eb x))
    (hFr : ∀ y, eO (Fr y) = Fr' (eO y))
    (hv : ∀ g, vdet' (Matrix.GeneralLinearGroup.map eK.toRingHom g) = vdet g) :
    ∃ (Ψ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B],
        (∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x)) →
          (OmegaNrObj (K := K) π Onr B ≃ OmegaNrObj (K := K') π' Onr' B)),
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
          (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
          (x : OmegaNrObj (K := K) π Onr B) (y : Onr'), (Ψ B hB x).1 y = x.1 (eO.symm y)) ∧
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
          (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
          (g : Matrix.GeneralLinearGroup (Fin 2) K) (x x' : OmegaNrObj (K := K) π Onr B),
        OmegaNr.IsTwistedAct π' Onr' Fr' vdet' B (Matrix.GeneralLinearGroup.map eK.toRingHom g) (Ψ B hB x) (Ψ B hB x') ↔
          OmegaNr.IsTwistedAct π Onr Fr vdet B g x x') ∧
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
          (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
          (g : Matrix.GeneralLinearGroup (Fin 2) K) (x x' : OmegaNrObj (K := K) π Onr B),
        DeligneDatum.IsPullback (K := K') (π := π') B (Matrix.GeneralLinearGroup.map eK.toRingHom g) (Ψ B hB x).2 (Ψ B hB x').2 ↔
          DeligneDatum.IsPullback (K := K) (π := π) B g x.2 x'.2) ∧
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
          (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
          (B₁ : Type) [CommRing B₁] [Algebra 𝒪 B₁] [Algebra 𝒪' B₁]
          (hB₁ : ∀ x : 𝒪, algebraMap 𝒪 B₁ x = algebraMap 𝒪' B₁ (eb x))
          (f : B →ₐ[𝒪] B₁) (f' : B →ₐ[𝒪'] B₁) (_ : ∀ b, f b = f' b)
          (x : OmegaNrObj (K := K) π Onr B) (x₁ : OmegaNrObj (K := K) π Onr B₁),
        DeligneDatum.IsBaseChange (K := K') (π := π') f' (Ψ B hB x).2 (Ψ B₁ hB₁ x₁).2 ↔
          DeligneDatum.IsBaseChange (K := K) (π := π) f x.2 x₁.2) := by sorry
