-- Prove2me | Theorems.Thm_AutomorphicForm_integrableOn_and_setIntegral_mul_constantTerm_finsum_borelSigmaConjClassOrbit_eq_inv_measure_mul_tsum_integral_integral
-- name    : AutomorphicForm.integrableOn_and_setIntegral_mul_constantTerm_finsum_borelSigmaConjClassOrbit_eq_inv_measure_mul_tsum_integral_integral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/ede90d57-00be-5f3e-ac50-87da65309323
-- title:
--   Constant term of an upper-triangular twisted class as orbital integrals
-- statement:
--   Let $K \subseteq L$ be fields with $L$ a number field, finite over $K$, write $\mathbb{A} = \mathbb{A}_L$ for the adele ring of $L$, let $\nu$ be a Haar measure on the Borel-measurable idele group $\mathbb{A}^{\times}$, and let $\Omega \subseteq \mathbb{A}^{\times}$ be a fundamental domain for the image of $L^{\times}$ in $\mathbb{A}^{\times}$ with respect to $\nu$. Let $D$ be a descent datum, i.e. a homomorphism from $\mathrm{Aut}(L/K)$ to the ring automorphisms of $\mathbb{A}$ that is continuous and compatible with the Galois action on principal adeles, let $\sigma \in \mathrm{Aut}(L/K)$, and write $\sigma_{\mathbb{A}}$ for the entrywise automorphism of $\mathrm{GL}_2(\mathbb{A})$ induced by $D.\mathrm{act}\,\sigma$, $\iota$ for the map $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb{A})$ induced by $L \to \mathbb{A}$, $c(z) = \mathrm{diag}(z,z)$, and $n(t) = \begin{pmatrix} 1 & t \\ 0 & 1\end{pmatrix}$. Let $\xi$ be a homomorphism from the full subgroup $\mathbb{A}^{\times}$ to $\mathbb{C}^{\times}$, continuous as a $\mathbb{C}$-valued function and trivial on the image of $L^{\times}$. Let $t' \in \mathrm{GL}_2(L)$ have vanishing off-diagonal entries and satisfy $N_{L/K}(t'_{00}/t'_{11}) \ne 1$; let $J$ be the set of $\gamma \in \mathrm{GL}_2(L)$ for which there is $b$ with $b_{10} = 0$ and $t'^{-1} b^{-1} \gamma\, \sigma(b)$ central, and $M$ the subgroup of those $m$ with both off-diagonal entries zero and $t'^{-1} m t' \sigma(m)^{-1}$ central. Let $a : \kappa \to \mathrm{GL}_2(L)$ take values in matrices with vanishing off-diagonal entries and be such that every such matrix $d$ satisfies $(a_j)^{-1} d \in M$ for exactly one $j$. Finally let $\varphi : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ be continuous with compact support and $x \in \mathrm{GL}_2(\mathbb{A})$. Put $x_j = \iota(a_j)^{-1} x$ and $F_j(w,t) = \varphi\bigl(x_j^{-1}\, \iota(t')\, \sigma_{\mathbb{A}}(n(t)\, c(w)\, x_j)\bigr)$, and let $\mu$ be the additive Haar measure on $\mathbb{A}$ and $\mu_B$ its conditional probability measure on the adelic box $B \subseteq \mathbb{A}$ (the product of the fundamental domain of the Minkowski lattice at the infinite places with the integral finite adeles). The conclusion is the conjunction of six assertions: the set of $j \in \kappa$ for which $F_j(w,t) \ne 0$ for some $w, t$ is finite; for all $j$ and $w$ the function $t \mapsto F_j(w,t)$ is $\mu$-integrable; for all $j$ the function $w \mapsto \xi(w) \int F_j(w,t)\, d\mu(t)$ is $\nu$-integrable; for every $z \in \mathbb{A}^{\times}$ the function $q \mapsto \sum^{\mathrm{f}}_{\gamma \in J} \varphi\bigl(x^{-1} \iota(\gamma)\, \sigma_{\mathbb{A}}(n(q)\, c(z)\, x)\bigr)$ (a finite-support sum) is $\mu_B$-integrable; the function $z \mapsto \xi(z) \int \sum^{\mathrm{f}}_{\gamma \in J} \varphi\bigl(x^{-1} \iota(\gamma)\, \sigma_{\mathbb{A}}(n(q)\, c(z)\, x)\bigr) d\mu_B(q)$, i.e. $\xi$ times the $\mu_B$-constant term along $n$ of $y \mapsto \sum^{\mathrm{f}}_{\gamma \in J} \varphi(x^{-1}\iota(\gamma)\sigma_{\mathbb{A}}(y))$ evaluated at $c(z)x$, is $\nu$-integrable on $\Omega$; and its integral over $\Omega$ equals $\mu(B)^{-1} \sum_{j} \int \xi(w) \int F_j(w,t)\, d\mu(t)\, d\nu(w)$, the real number $\mu(B)$ being read as a complex scalar.
--
--   This is the per-cusp unfolding of the constant term attached to one regular (norm-non-trivial) upper-triangular twisted conjugacy class in the geometric side of the twisted trace formula for $\mathrm{GL}_2$ over $L/K$: the idele-class fold of the constant term of the kernel sum over $J$ is rewritten, pointwise in $x$, as a sum of twisted unipotent orbital integrals indexed by representatives of the diagonal torus modulo $M$. It is used in the assembly of the truncated hyperbolic contribution, where it feeds the comparison of the constant term high in the cusp with the corresponding orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrableOn_and_setIntegral_mul_constantTerm_finsum_borelSigmaConjClassOrbit_eq_inv_measure_mul_tsum_integral_integral.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

theorem AutomorphicForm.integrableOn_and_setIntegral_mul_constantTerm_finsum_borelSigmaConjClassOrbit_eq_inv_measure_mul_tsum_integral_integral
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (t' : GL (Fin 2) L) (ht'u : (t' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht'l : (t' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0 / (t' : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (J : Set (GL (Fin 2) L))
    (hJ : ∀ γ, γ ∈ J ↔ ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      t'⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L))
    (M : Subgroup (GL (Fin 2) L))
    (hM : ∀ m, m ∈ M ↔ ((m : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (m : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      t'⁻¹ * (m * t' * (Matrix.GeneralLinearGroup.map (σ : L →+* L) m)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {κ : Type} (a : κ → GL (Fin 2) L)
    (haD : ∀ j, ((a j : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      ((a j : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (ha : ∀ d : GL (Fin 2) L, (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (d : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      ∃! j, (a j)⁻¹ * d ∈ M)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    {j : κ | ∃ (w : (AdeleRing (𝓞 L) L)ˣ) (t : AdeleRing (𝓞 L) L),
        φ (((AutomorphicForm.globalPoints (𝓞 L) L (a j))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t' *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.unipotentGL2 t *
            (AutomorphicForm.centralScalar (𝓞 L) L w * ((AutomorphicForm.globalPoints (𝓞 L) L (a j))⁻¹ * x)))) ≠
          0}.Finite ∧
    (∀ (j : κ) (w : (AdeleRing (𝓞 L) L)ˣ), Integrable (fun t : AdeleRing (𝓞 L) L =>
        φ (((AutomorphicForm.globalPoints (𝓞 L) L (a j))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t' *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.unipotentGL2 t *
            (AutomorphicForm.centralScalar (𝓞 L) L w * ((AutomorphicForm.globalPoints (𝓞 L) L (a j))⁻¹ * x)))))
        (adelicAddHaar (𝓞 L) L)) ∧
    (∀ j : κ, Integrable (fun w : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ) *
        ∫ t, φ (((AutomorphicForm.globalPoints (𝓞 L) L (a j))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t' *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.unipotentGL2 t *
            (AutomorphicForm.centralScalar (𝓞 L) L w * ((AutomorphicForm.globalPoints (𝓞 L) L (a j))⁻¹ * x))))
          ∂(adelicAddHaar (𝓞 L) L)) νZL) ∧
    (∀ z : (AdeleRing (𝓞 L) L)ˣ, Integrable (fun q : AdeleRing (𝓞 L) L =>
        ∑ᶠ γ ∈ J, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.unipotentGL2 q * (AutomorphicForm.centralScalar (𝓞 L) L z * x))))
        (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))) ∧
    IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        @AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
          (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ γ ∈ J, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
            AutomorphicForm.sigmaAdelicAct K L D σ y))
          (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ΩL νZL ∧
    (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        @AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
          (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ γ ∈ J, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
            AutomorphicForm.sigmaAdelicAct K L D σ y))
          (AutomorphicForm.centralScalar (𝓞 L) L z * x) ∂νZL) =
      ((adelicAddHaar (𝓞 L) L (adelicBox L)).toReal : ℂ)⁻¹ *
        ∑' j : κ, ∫ w, ((ξL ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ) *
          ∫ t, φ (((AutomorphicForm.globalPoints (𝓞 L) L (a j))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t' *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.unipotentGL2 t *
              (AutomorphicForm.centralScalar (𝓞 L) L w * ((AutomorphicForm.globalPoints (𝓞 L) L (a j))⁻¹ * x))))
            ∂(adelicAddHaar (𝓞 L) L) ∂νZL := by sorry
