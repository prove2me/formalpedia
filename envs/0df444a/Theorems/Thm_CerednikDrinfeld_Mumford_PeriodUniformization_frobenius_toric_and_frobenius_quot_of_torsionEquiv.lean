-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_PeriodUniformization_frobenius_toric_and_frobenius_quot_of_torsionEquiv
-- name    : CerednikDrinfeld.Mumford.PeriodUniformization.frobenius_toric_and_frobenius_quot_of_torsionEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/f99f8332-c607-5788-ac20-13d069d88651
-- title:
--   Frobenius on p-torsion of a Mumford period uniformisation
-- statement:
--   Let $p\neq r$ be primes, let $E,V$ be finite types, let $D$ be a degeneracy datum on $(E,V)$ (two maps $a,b:E\to V$ and weights $w:E\to\mathbb{N}_{>0}$) and $H$ Hecke data for $D$ (commuting matrices $T_\ell$ on $E$ and $T_\ell^{v}$ on $V$, equivariant for the joint degeneracy maps outside a finite set of primes and stabilising their joint kernel, the ribbon kernel $Z=\mathrm{ribbonKernel}\,D\subseteq(E\to\mathbb{Z})$). Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $r$ a nonunit of $A$, let $T$ be an abelian group carrying a ring homomorphism $\mathrm{hecke}$ from $\mathrm{HeckeAlg}=\mathbb{Z}[X_\ell:\ell\text{ prime}]$ to $\mathrm{End}_{\mathbb{Z}}T$ and a homomorphism $\mathrm{gal}$ from $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to $\mathrm{AddAut}\,T$, and let $\mathcal{U}$ be a period uniformisation of $(T,\mathrm{hecke},\mathrm{gal})$ at $A$ over $(D,H)$: a subfield $K$ of the completion $C_A$ of $A$ at its valuation with a valuation homomorphism $\mathrm{ord}$, inertia-invariance and Hensel properties, a period datum $P$ with symmetric pairing $Q:Z\times Z\to\mathrm{Additive}\,K^\times$ whose $\mathrm{ord}$ is the ribbon Gram form, Hecke-adjointable and with decomposition-invariant period values, and a homomorphism $e$ from the subgroup $U$ of $P.\mathrm{TorusPoints}=\mathrm{Hom}_{\mathbb{Z}}(Z,\mathrm{Additive}\,C_A^\times)$ to $T$ which hits all torsion, has torsion image, has kernel the period lattice (the range of $\mathcal{U}.P.QL$), and is compatible with Hecke operators, inertia and Frobenius. Let $\zeta\in C_A^\times$ be a primitive $p$-th root of unity and let $\chi$ be an additive isomorphism from the $p$-torsion $U[p]=\mathrm{torsionBy}_{\mathbb{Z}}(U,p)$ onto $\mathrm{Hom}_{\mathbb{Z}}(Z,\mathbb{Z}/p)$ such that $v(z)=\zeta^{\chi(v)(z)}$ (multiplicatively) for all $v\in U[p]$, $z\in Z$. Write $T_r|_Z=\mathrm{heckeKernelMap}\,H\,r$ for the restriction of $T_r$ to $Z$. Then two statements hold. First, for every $\varphi\in\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ which is a Frobenius at $A$ for $r$ (it lies in the decomposition subgroup of $A$ and acts on the residue field of $A$ by $x\mapsto x^{r}$) and every $v\in U[p]$ there is $v'\in U[p]$ with $\mathrm{gal}(\varphi)(e(v))=e(v')$ and $\chi(v')=r\cdot(\chi(v)\circ T_r|_Z)$. Second, for every such $\varphi$, every $u\in U$ and $x\in Z$ with $p\,u=\mathcal{U}.P.QL\,x$ in $P.\mathrm{TorusPoints}$, and given that the precomposition $u\circ T_r|_Z$ again lies in $U$, there is $v\in U$ with $p\,v=0$ and $\mathrm{gal}(\varphi)(e(u))=e(u\circ T_r|_Z)+e(v)$.
--
--   This is the Frobenius part of the passage from a Mumford-style period uniformisation at a prime $r$ to a purely toric description of the $p$-torsion and of the $p$-division points, in the style of the Čerednik–Drinfeld description of Frobenius on the character group of the torus. It is used by [`CerednikDrinfeld.Mumford.nonempty_toricUniformization_of_periodUniformization`](thm.html#CerednikDrinfeld.Mumford.nonempty_toricUniformization_of_periodUniformization) to supply the Frobenius compatibility fields of a toric uniformisation, the Hecke action on $U$ being precomposition with the kernel Hecke maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_PeriodUniformization_frobenius_toric_and_frobenius_quot_of_torsionEquiv.lean

import Definitions.Def_CerednikDrinfeld_MumfordUniformization
import Definitions.Def_CerednikDrinfeld_ToricUniformization
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford ModularCurve

theorem CerednikDrinfeld.Mumford.PeriodUniformization.frobenius_toric_and_frobenius_quot_of_torsionEquiv
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hpr : p ≠ r)
    {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
    {D : DegeneracyData E V} {H : HeckeData D}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime r}
    {T : Type} [AddCommGroup T] {hecke : HeckeAlg →+* Module.End ℤ T}
    {gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T}
    (𝒰 : PeriodUniformization r D H A hA T hecke gal)
    (ζ : (A.valuation.Completion)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (χ : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ)) ≃+ (↥(ribbonKernel D) →ₗ[ℤ] ZMod p))
    (hχ : ∀ (v : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ))) (z : ↥(ribbonKernel D)),
      Additive.toMul ((((v : ↥𝒰.P.U) : 𝒰.P.TorusPoints) z)) = ζ ^ (χ v z).val) :
    (∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt φ r →
      ∀ v : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ)), ∃ v' : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ)),
        gal φ (𝒰.e (v : ↥𝒰.P.U)) = 𝒰.e (v' : ↥𝒰.P.U) ∧
          χ v' = (r : ℤ) • ((χ v) ∘ₗ heckeKernelMap H ⟨r, Fact.out⟩)) ∧
    (∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt φ r →
      ∀ (u : ↥𝒰.P.U) (x : ↥(ribbonKernel D)), (p : ℤ) • (u : 𝒰.P.TorusPoints) = 𝒰.P.QL x →
        ∀ hu : 𝒰.P.precomp (heckeKernelMap H ⟨r, Fact.out⟩) (u : 𝒰.P.TorusPoints) ∈ 𝒰.P.U,
          ∃ v : ↥𝒰.P.U, (p : ℤ) • v = 0 ∧
            gal φ (𝒰.e u) = 𝒰.e ⟨𝒰.P.precomp (heckeKernelMap H ⟨r, Fact.out⟩) (u : 𝒰.P.TorusPoints), hu⟩ + 𝒰.e v) := by sorry
