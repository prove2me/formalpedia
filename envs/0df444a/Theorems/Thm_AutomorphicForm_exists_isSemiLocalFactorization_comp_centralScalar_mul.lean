-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isSemiLocalFactorization_comp_centralScalar_mul
-- name    : AutomorphicForm.exists_isSemiLocalFactorization_comp_centralScalar_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/e9a1ce29-cedf-5cac-9c1e-79ab4a7c5559
-- title:
--   Central translation preserves semi-local factorisation, after enlarging S
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $S$ be a finite set of height-one primes of $\mathcal O_K$, and let $\varphi$ on $\mathrm{GL}_2$ of the adele ring of $L$, $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adele ring of $L$, $\varphi_f$ on $\mathrm{GL}_2$ of the finite adele ring of $L$, and a family $\varphi_{S,v}$ on $\mathrm{GL}_2(L\otimes_K K_v)$ indexed by the height-one primes $v$ of $\mathcal O_K$, be complex-valued functions forming a semi-local factorisation at $S$: $\varphi_a$ is the restriction to $\mathrm{GL}_2$ of a smooth function of the archimedean matrix entries and has compact support, $\varphi_f$ is locally constant with compact support, each $\varphi_{S,v}$ for $v\in S$ is locally constant with compact support, $\varphi_f(h)=\prod_{v\in S}\varphi_{S,v}$ evaluated at the semi-local component of $h$ at $v$ whenever all semi-local components of $h$ at primes outside $S$ lie in the integral set (the matrix and its inverse have entries in the image of $\mathcal O_L\otimes\mathcal O_{K_v}$), $\varphi_f(h)=0$ as soon as some component outside $S$ fails to be integral in this sense, and $\varphi(g)=\varphi_a(g_\infty)\varphi_f(g_f)$. Then for every unit $z$ of the adele ring of $L$ there is a finite set $S_1$ of height-one primes containing $S$ such that the translated data again form a semi-local factorisation at $S_1$, namely $g\mapsto\varphi(\mathrm{diag}(z,z)\,g)$, $y\mapsto\varphi_a(\mathrm{diag}(z_\infty,z_\infty)\,y)$, $h\mapsto\varphi_f(\mathrm{diag}(z_f,z_f)\,h)$, and, at each $v$, $x\mapsto \psi_v(\mathrm{diag}(z_v,z_v)\,x)$ where $z_v$ is the image of $z_f$ under the semi-local evaluation map at $v$, and $\psi_v=\varphi_{S,v}$ for $v\in S$ while $\psi_v$ is the indicator function, with value $1$, of the integral set in $\mathrm{GL}_2(L\otimes_K K_v)$ for $v\notin S$.
--
--   This records that the class of semi-local factorisations of adelic test functions on $\mathrm{GL}_2$ over $L$ is stable under left translation by a central idelic scalar, at the cost of enlarging the exceptional finite set of primes of $K$ to absorb the places where the idele is not integrally invertible. It feeds the estimate for orbital integrals over double cosets, [`AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure`](thm.html#AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure), where central translates of a fixed factorisable test function have to be handled uniformly.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isSemiLocalFactorization_comp_centralScalar_mul.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isSemiLocalFactorization_comp_centralScalar_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S₁ ∧
      AutomorphicForm.IsSemiLocalFactorization K L S₁
        (fun g => φ (AutomorphicForm.centralScalar (𝓞 L) L z * g))
        (fun y => φa (Matrix.GeneralLinearGroup.scalar (Fin 2)
          (Units.map (AdelicLevel.adeleArch (𝓞 L) L).toMonoidHom z) * y))
        (fun h => φf (Matrix.GeneralLinearGroup.scalar (Fin 2)
          (Units.map (AdelicLevel.adeleFin (𝓞 L) L).toMonoidHom z) * h))
        (fun v x => (if v ∈ S then φS v
            else (AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
          (Matrix.GeneralLinearGroup.scalar (Fin 2)
            (Units.map (AutomorphicForm.semiLocalEval K L v).toMonoidHom
              (Units.map (AdelicLevel.adeleFin (𝓞 L) L).toMonoidHom z)) * x)) := by sorry
