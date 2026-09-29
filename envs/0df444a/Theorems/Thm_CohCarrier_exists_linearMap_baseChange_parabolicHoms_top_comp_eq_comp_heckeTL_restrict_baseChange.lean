-- Prove2me | Theorems.Thm_CohCarrier_exists_linearMap_baseChange_parabolicHoms_top_comp_eq_comp_heckeTL_restrict_baseChange
-- name    : CohCarrier.exists_linearMap_baseChange_parabolicHoms_top_comp_eq_comp_heckeTL_restrict_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/1c89eab1-3248-595f-af3c-1f99698814dd
-- title:
--   Base change of parabolic cohomology with Hecke operators
-- statement:
--   Fix $N\ge 1$ (as a natural number with `NeZero N`), a field $K$ of characteristic zero and a field $\Omega$ equipped with a $K$-algebra structure. Write $\Gamma=$ [`CohCarrier.GammaH N ⊤`](def/CohCarrier_Level.html#L133), the image in $SL(2,\mathbb Z)$ of the preimage of the full subgroup $\top\le(\mathbb Z/N)^{\times}$ under the determinant-type character `gamma0Units` of $\Gamma_0(N)$, so $\Gamma=\Gamma_0(N)$; for an abelian group $A$ put $H^1(A)=$ [`CohCarrier.H1 N ⊤ A`](def/CohCarrier_Level.html#L162) $=\operatorname{Hom}(\mathrm{Additive}\,\Gamma,A)$, let $\mathrm{par}_R(A)\subseteq H^1(A)$ be the $R$-submodule of those $\varphi$ with $\varphi(\gamma)=0$ for every $\gamma\in\Gamma$ whose matrix has $\operatorname{trace}^2=4$, and for $\ell\ge 1$ let [`CohCarrier.heckeTL N ⊤ A ℓ`](def/CohCarrier_Inst.html#L23) be the endomorphism of $H^1(A)$ sending $\varphi$ to the transfer (`coresAdd`) of the composite of $\varphi$ with the additive form of the conjugation homomorphism `conjL N ⊤ ℓ`. The assertion is that there exist: a proof `hpar` that for every prime $p$ and every $w\in H^1(K)$ lying in $\mathrm{par}_K(K)$ the element `heckeTL N ⊤ K p` $w$ again lies in $\mathrm{par}_K(K)$; and an $\Omega$-linear map $\Phi:\Omega\otimes_K \mathrm{par}_K(K)\to H^1(\Omega)$, such that (i) for all primes $p,p'$ the restrictions of `heckeTL N ⊤ K p` and `heckeTL N ⊤ K p'` to $\mathrm{par}_K(K)$ commute, (ii) $\Phi$ is injective, (iii) the range of $\Phi$ is exactly $\mathrm{par}_\Omega(\Omega)$, and (iv) for every prime $p$, `heckeTL N ⊤ Ω p` $\circ\;\Phi=\Phi\circ$ (the base change to $\Omega$ of the restriction of `heckeTL N ⊤ K p` to $\mathrm{par}_K(K)$).
--
--   This is the compatibility of parabolic group cohomology of $\Gamma_0(N)$ (equivalently, of modular symbols) with extension of scalars between fields of characteristic zero, together with the commutativity of the transfer Hecke operators at primes and their equivariance under that extension. It is used to transport eigenspaces and generalised eigenspaces of the Hecke operators from $K$ to $\Omega$ without change of dimension, in the computation of the rank of intersections of such eigenspaces inside the parabolic part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_linearMap_baseChange_parabolicHoms_top_comp_eq_comp_heckeTL_restrict_baseChange.lean

import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem CohCarrier.exists_linearMap_baseChange_parabolicHoms_top_comp_eq_comp_heckeTL_restrict_baseChange
    (N : ℕ) [NeZero N] (K : Type) [Field K] [CharZero K] (Ω : Type) [Field Ω] [Algebra K Ω] :
    ∃ (hpar : ∀ (p : ℕ) (hp : p.Prime) (w : CohCarrier.H1 N ⊤ K),
        w ∈ ModularCurve.Period.parabolicHoms K (CohCarrier.GammaH N ⊤) K →
          (haveI : NeZero p := ⟨hp.ne_zero⟩; CohCarrier.heckeTL N ⊤ K p) w ∈
            ModularCurve.Period.parabolicHoms K (CohCarrier.GammaH N ⊤) K)
      (Φ : Ω ⊗[K] ↥(ModularCurve.Period.parabolicHoms K (CohCarrier.GammaH N ⊤) K) →ₗ[Ω]
        CohCarrier.H1 N ⊤ Ω),
      (∀ (p p' : ℕ) (hp : p.Prime) (hp' : p'.Prime),
        Commute ((haveI : NeZero p := ⟨hp.ne_zero⟩; CohCarrier.heckeTL N ⊤ K p).restrict (hpar p hp))
          ((haveI : NeZero p' := ⟨hp'.ne_zero⟩; CohCarrier.heckeTL N ⊤ K p').restrict (hpar p' hp'))) ∧
      Function.Injective Φ ∧
      LinearMap.range Φ = ModularCurve.Period.parabolicHoms Ω (CohCarrier.GammaH N ⊤) Ω ∧
      ∀ (p : ℕ) (hp : p.Prime),
        (haveI : NeZero p := ⟨hp.ne_zero⟩; CohCarrier.heckeTL N ⊤ Ω p) ∘ₗ Φ =
          Φ ∘ₗ ((haveI : NeZero p := ⟨hp.ne_zero⟩; CohCarrier.heckeTL N ⊤ K p).restrict (hpar p hp)).baseChange Ω := by sorry
