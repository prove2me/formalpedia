-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_forall_mem_of_orbital_partAt_ne_zero_of_mem_unitIdelesOutside
-- name    : AutomorphicForm.exists_isCompact_forall_mem_of_orbital_partAt_ne_zero_of_mem_unitIdelesOutside
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/0267ca16-c821-582f-b32c-b01ce06db301
-- title:
--   Non-vanishing orbital integrals confine the idele to a compact set
-- statement:
--   Let $K$ be a number field, $S$ a finite set of finite places of $K$, and $u \in K^\times$. For an idele $z \in \mathbb{A}_K^\times$ put $\gamma(z) = c(z)\cdot\mathrm{diag}(\iota u, 1) \in GL_2(\mathbb{A}_K)$, where $c(z)$ is the scalar matrix with entry $z$ and $\iota : K^\times \to \mathbb{A}_K^\times$ is induced by the structure map; write $\gamma(z)_\infty$ for its image under `AdelicLevel.glArch` and $\gamma(z)_v$ for the image of its finite part under `AdelicLevel.finComponent` at $v$. Assume given: a function $f_\infty$ on $GL_2(K_\infty)$ which has compact support and is of the form $g \mapsto \Phi(\text{entries of } g)$ for some $C^\infty$ function $\Phi$ on $2\times 2$ matrices over the mixed space of $K$; functions $f_v$ on $GL_2(K_v)$ which for $v \in S$ are locally constant with compact support; a Borel measure $\nu_A$ on $GL_2(K_\infty)$; Borel measures $\tau_A(z)$ on the centraliser of $\gamma(z)_\infty$ and $\tau_F(z,v)$ on the centraliser of $\gamma(z)_v$; and complex numbers $I_\infty(z)$, $I_v(z)$ such that $I_\infty(z)$ is an orbital-integral value $\int f_\infty(x^{-1}\gamma(z)_\infty x)\,w(x)\,d\nu_A$ for some non-negative measurable compactly supported weight $w$ with $\int_{Z(\gamma(z)_\infty)} w(tx)\,d\tau_A(z) = 1$ whenever $f_\infty(x^{-1}\gamma(z)_\infty x) \neq 0$, and, for $v \in S$, $I_v(z)$ is the analogous orbital-integral value of $f_v$ at $\gamma(z)_v$ against the fixed Haar measure `localHaar` on $GL_2(K_v)$ and the measure $\tau_F(z,v)$. Then there is a compact set $T \subseteq \mathbb{A}_K^\times$ containing every idele $z$ such that, for all $v \notin S$, the $v$-components of the finite parts of $z$ and of $z^{-1}$ lie in $\mathcal{O}_v$, and such that the truncated idele $z_S =$ [`NumberField.Idele.partAt K S z`](def/NumberField_IdeleProductMeasure.html#L90) satisfies $I_\infty(z_S) \neq 0$ and $I_v(z_S) \neq 0$ for all $v \in S$.
--
--   This is the properness statement underlying the convergence of the comparison of trace formulae for $GL(2)$: non-vanishing of the local orbital integrals along the split classes $c(z)\,\mathrm{diag}(u,1)$ bounds the determinant $z^2u$ inside the supports of the test functions, so the relevant ideles range over a compact set. It is used to prove integrability of the product of the archimedean and finite orbital integrals over the idele group, in [`AutomorphicForm.integrable_mul_orbital_mul_prod_orbital_sPart_of_isArchTestFactor_of_isLocalTestFn`](thm.html#AutomorphicForm.integrable_mul_orbital_mul_prod_orbital_sPart_of_isArchTestFactor_of_isLocalTestFn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_forall_mem_of_orbital_partAt_ne_zero_of_mem_unitIdelesOutside.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in

theorem AutomorphicForm.exists_isCompact_forall_mem_of_orbital_partAt_ne_zero_of_mem_unitIdelesOutside
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (u : Kˣ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : AutomorphicForm.IsArchTestFactor K fa)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfS : ∀ v ∈ S, AutomorphicForm.IsLocalTestFn K v (fS v))
    (νA : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (τA : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (τF : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))))
    (IA : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIA : ∀ z, AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA z) fa (IA z))
    (IF : (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIF : ∀ z, ∀ v ∈ S, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF z v) (fS v) (IF z v)) :
    ∃ T : Set (AdeleRing (𝓞 K) K)ˣ, IsCompact T ∧
      ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S : Set (HeightOneSpectrum (𝓞 K))) →
        IA (NumberField.Idele.partAt K S z) ≠ 0 →
        (∀ v ∈ S, IF (NumberField.Idele.partAt K S z) v ≠ 0) →
          z ∈ T := by sorry
