-- Prove2me | Theorems.Thm_CuspForm_IsNewform_exists_linearMap_fixedSubmodule_H1_gammaH_laws_of_isCuspidalOfType
-- name    : CuspForm.IsNewform.exists_linearMap_fixedSubmodule_H1_gammaH_laws_of_isCuspidalOfType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/2a9a2e63-6581-563c-b143-b4fed8c5f3e9
-- title:
--   Cuspidal K(q)-type of a newform inside H¹(Γ_H(Nq²),ℂ)
-- statement:
--   Let $N\ge 1$, let $q$ be a prime with $q\nmid N$, and let $g$ be a weight-two cusp form on $\Gamma_0(Nq^2)$ which is a newform in the sense of the project (a normalised eigenform no good eigensystem of which occurs at a proper divisor of $Nq^2$). Let $\Phi$ be a function on $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$ of which $g$ is an adelic lift: $\Phi$ is left invariant under the global points, right invariant under the finite level-one subgroup attached to the rational level $Nq^2$, and at points with trivial finite part and totally positive archimedean part it is given by $(g\mid_2 \alpha)(i)$ for the archimedean component $\alpha$. Let $V$ be a complex vector space with a $\mathbb{C}$-commuting action of $\mathrm{GL}_2(\mathbb{Q}_q)$ whose submodule $W$ of vectors fixed by the $q$-adic congruence subgroup $\mathrm{gl2CongruenceSubgroup}\,q\,1$ (matrices $g$ with all entries of $g-1$ and of $g^{-1}-1$ of norm at most $q^{-1}$) is finite dimensional over $\mathbb{C}$; let $f\colon V\to \mathrm{AdelicSpan}\,\Phi$ be an injective $\mathrm{GL}_2(\mathbb{Q}_q)$-equivariant linear map whose range is the $\mathbb{C}$-span of the $\mathrm{GL}_2(\mathbb{Q}_q)$-translates of the distinguished element $\mathrm{AdelicSpan.self}\,\Phi$. Let $\theta\colon \mathbb{F}_{q^2}^\times\to\mathbb{C}^\times$ be a character and assume that the representation $\mathrm{gl2ReductionRep}\,q\,V$ of $\mathrm{GL}_2(\mathbb{Z}/q)$ on $W$ is cuspidal of type $\theta$: $\dim_\mathbb{C} W=q-1$, no non-zero vector is fixed by all unipotents, the scalar matrices act as the identity, and for every $\alpha\in\mathbb{F}_{q^2}^\times$ the characteristic polynomial of the torus element times $(X-\theta(\alpha))(X-\theta(\alpha)^{-1})$ equals that of the induced representation at the same element. Let $\mathrm{red}\colon \Gamma_0(N)\to \mathrm{GL}_2(\mathbb{Z}/q)$ be the inclusion into $\mathrm{SL}_2(\mathbb{Z})$ followed by reduction modulo $q$. Write $H\le(\mathbb{Z}/Nq^2)^\times$ for the kernel of reduction to $(\mathbb{Z}/q)^\times$ and $\Gamma_H(Nq^2)\le\mathrm{SL}_2(\mathbb{Z})$ for the matrices in $\Gamma_0(Nq^2)$ whose associated unit lies in $H$. Then there exists a $\mathbb{C}$-linear map $\Psi$ from $W$ to the space of additive homomorphisms $\Gamma_H(Nq^2)\to\mathbb{C}$ such that: (i) $\Psi\neq 0$; (ii) for every prime $\ell$ with $\ell\nmid Nq^2$ and $\ell\not\equiv 0 \bmod q$, and every $w\in W$, the transfer Hecke operator satisfies $T_\ell(\Psi w)=a_\ell(g)\,\Psi(\mathrm{diag}(\ell,1)\cdot w)$, where $a_\ell(g)$ is the $\ell$-th coefficient of the level-one $q$-expansion of $g$ and $\mathrm{diag}(\ell,1)\in\mathrm{GL}_2(\mathbb{Z}/q)$ acts through $\mathrm{gl2ReductionRep}\,q\,V$; and (iii) for every group homomorphism $\mathrm{conj}\colon \ker(\mathrm{red})\to\Gamma_H(Nq^2)$ satisfying, entrywise, $(\mathrm{conj}\,x)_{00}=x_{00}$, $q\,(\mathrm{conj}\,x)_{01}=x_{01}$, $(\mathrm{conj}\,x)_{10}=q\,x_{10}$ and $(\mathrm{conj}\,x)_{11}=x_{11}$, and for all $\gamma,y\in\Gamma_0(N)$ with $y$ and $\gamma y\gamma^{-1}$ in $\ker(\mathrm{red})$ and all $w\in W$, one has $\Psi(\mathrm{red}(\gamma)\cdot w)(\mathrm{conj}(\gamma y\gamma^{-1}))=\Psi(w)(\mathrm{conj}\,y)$.
--
--   This is the Eichler–Shimura occurrence of the $K(q)$-type of a weight-two newform on $\Gamma_0(Nq^2)$ in the trivial-coefficient cohomology $H^1(\Gamma_H(Nq^2),\mathbb{C})=\operatorname{Hom}(\Gamma_H(Nq^2),\mathbb{C})$, packaged as a non-zero linear family indexed by the cuspidal representation of type $\theta$, together with a twisted Hecke eigenvalue law and the conjugation equivariance coming from $\Gamma_H(Nq^2)\cong\Gamma(q)\cap\Gamma_0(N)$ after conjugation by $\mathrm{diag}(q,1)$. It feeds the construction of a non-zero linear functional on $H^1$ realising the Hecke eigensystem of $g$ on the type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNewform_exists_linearMap_fixedSubmodule_H1_gammaH_laws_of_isCuspidalOfType.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ReductionFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup

theorem CuspForm.IsNewform.exists_linearMap_fixedSubmodule_H1_gammaH_laws_of_isCuspidalOfType
    (N : ℕ) [NeZero N] {q : ℕ} [Fact q.Prime] (hqN : ¬ q ∣ N)
    (g : CuspForm (Gamma0 (N * q ^ 2)) 2) (hg : g.IsNewform)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    [FiniteDimensional ℂ ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)]
    (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ) (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v)
    (hfi : Function.Injective f)
    (hfr : LinearMap.range f =
      Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (θ : (GaloisField q 2)ˣ →* ℂˣ) (hθ : CuspidalType.IsCuspidalOfType θ (LocalNewvector.gl2ReductionRep q V))
    (red : Gamma0 N →* CuspidalType.GL2 q)
    (hred : red = (Matrix.SpecialLinearGroup.toGL.comp
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype) :
    ∃ Ψ : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) →ₗ[ℂ]
        CohCarrier.H1 (N * q ^ 2) (ZMod.unitsMap ((dvd_pow_self q two_ne_zero).mul_left N)).ker ℂ,
      Ψ ≠ 0 ∧
      (∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q ^ 2 → ∀ h : ((ℓ : ZMod q) ≠ 0),
        ∀ w : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V),
          CohCarrier.heckeT (N * q ^ 2) (ZMod.unitsMap ((dvd_pow_self q two_ne_zero).mul_left N)).ker ℓ ℂ (Ψ w) =
            ModularFormClass.qCoeff g ℓ •
              Ψ (LocalNewvector.gl2ReductionRep q V (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) w)) ∧
      ∀ (conj : ↥red.ker →*
          ↥(CohCarrier.GammaH (N * q ^ 2) (ZMod.unitsMap ((dvd_pow_self q two_ne_zero).mul_left N)).ker)),
        (∀ x : ↥red.ker,
          (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 =
            ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 ∧
          (q : ℤ) * (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 =
            ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 ∧
          (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 =
            (q : ℤ) * ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 ∧
          (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1 =
            ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1) →
        ∀ (γ y : Gamma0 N) (hy : y ∈ red.ker) (hy' : γ * y * γ⁻¹ ∈ red.ker)
          (w : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)),
          Ψ (LocalNewvector.gl2ReductionRep q V (red γ) w) (Additive.ofMul (conj ⟨γ * y * γ⁻¹, hy'⟩)) =
            Ψ w (Additive.ofMul (conj ⟨y, hy⟩)) := by sorry
