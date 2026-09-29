-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isGenuineCuspRealizationAt_hasNewvectorConductor_adelicSpan_factorization_of_isPrimitiveForm_weightOne
-- name    : AutomorphicForm.exists_isGenuineCuspRealizationAt_hasNewvectorConductor_adelicSpan_factorization_of_isPrimitiveForm_weightOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/b80255d3-d252-59a7-8899-85d92ca330bc
-- title:
--   Windowed adelic realization of a weight-one primitive form
-- statement:
--   Fix reals $c,u,d_1,d_2$ with $c>0$ and $0<d_1<d_2$, and a finite set $T\subset \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$; write $D=\bigcup_{x\in T}\{g x : g\in \mathfrak{S}\}$, where $\mathfrak{S}=$ `centreCutSiegelSet ℚ c u d₁ d₂` consists of those $g$ whose finite part is integral, whose archimedean component has local height $\ge c$ at every infinite place, window coordinate $x$-part squared $\le u^2$, and archimedean determinant norm in $[d_1,d_2]$. Assume $D$ covers modulo the centre: every $g$ admits $\gamma\in\mathrm{GL}_2(\mathbb{Q})$ and an idelic scalar $z$ with $\gamma g z\in D$. Let $N\ge 1$, let $\psi$ be a Dirichlet character mod $N$ with values in $\mathbb{C}$, and let $f$ be a weight-one cusp form on $\Gamma_1(N)$ that is primitive for $\psi$ (normalised eigenform with the Hecke relations away from $N$, multiplicativity at primes dividing $N$ and nebentypus $\psi$, whose eigenpacket occurs at no proper divisor of $N$). Let $\Theta$ be a Hecke eigensystem over $\mathbb{Q}$ with complex values such that, outside a finite set of primes and outside the primes dividing $N$, $a_p(f)=\Theta.a(v)$ and $\psi(p)=\Theta.b(v)$ for every finite place $v$ containing $p$. Then there exist a Hecke eigensystem $\Theta'$ agreeing with $\Theta$ outside a finite set of places and a smooth cuspidal realization $R'$ of the raw central rescaling $\Theta'.\mathrm{toRawCentral}$ (same level and $a$, with $b(v)$ divided by $\#(\mathcal{O}/v)$) for the carrier pins `productionPinsOf` built from $D$, the level subgroups $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, the Hecke generators $\mathrm{heckeGen}(v)$ and the adelic box, such that $R'$ is genuine, i.e. its underlying function is continuous, and such that for every prime $q$ the $\mathbb{C}$-span of the $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$-translates of that function has newvector conductor $v_q(N)$ at $q$: the vectors fixed by $K_1(q^{v_q(N)})$ are nonzero, while those fixed by $K_1(q^m)$ vanish for all $m<v_q(N)$.
--
--   This packages a primitive weight-one cusp form as a continuous adelic cuspidal Hecke eigenfunction on a prescribed Siegel-type window, with the local conductors of its $\mathrm{GL}_2$-span given by the exact power of each prime in $N$, as in the newvector theory of Casselman and Li. It feeds the weight-one analytic estimate [`DeligneSerre.exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen`](thm.html#DeligneSerre.exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isGenuineCuspRealizationAt_hasNewvectorConductor_adelicSpan_factorization_of_isPrimitiveForm_weightOne.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm
  AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open CongruenceSubgroup
open scoped MatrixGroups ModularForm

theorem AutomorphicForm.exists_isGenuineCuspRealizationAt_hasNewvectorConductor_adelicSpan_factorization_of_isPrimitiveForm_weightOne
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf : CuspForm.IsPrimitiveForm ψ f)
    (Θ : HeckeEigensystem ℚ ℂ)
    (hΘ : ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ N →
      ∀ v : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∈ v.asIdeal →
        ModularFormClass.qCoeff f p = Θ.a v ∧ ψ (p : ZMod N) = Θ.b v) :
    ∃ (Θ' : HeckeEigensystem ℚ ℂ) (_ : Θ'.AgreesAwayFromFinite Θ)
      (R' : SmoothCuspRealizationAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) Θ'.toRawCentral),
      IsGenuineCuspRealizationAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) Θ'.toRawCentral R' ∧
      ∀ (q : ℕ) (_ : Fact q.Prime),
        LocalNewvector.HasNewvectorConductor q (LocalNewvector.AdelicSpan R'.toFun) (N.factorization q) := by sorry
